namespace FsAutoComplete

open System
open System.Diagnostics
open System.IO
open System.Text
open Microsoft.FSharp.Compiler.SourceCodeServices

type SymbolKind =
    | Ident
    | Operator
    | GenericTypeParameter
    | StaticallyResolvedTypeParameter
    | ActivePattern
    | Keyword
    | Other

type LexerSymbol =
    { Kind: SymbolKind
      Line: int
      LeftColumn: int
      RightColumn: int
      Text: string }
    member x.Range = x.Line, x.LeftColumn, x.Line, x.RightColumn

[<RequireQualifiedAccess>]
type SymbolLookupKind =
    | Fuzzy
    | ByRightColumn
    | ByLongIdent
    | Simple

type internal DraftToken =
    { Kind: SymbolKind
      Token: FSharpTokenInfo
      RightColumn: int }
    static member inline Create kind token =
        { Kind = kind; Token = token; RightColumn = token.LeftColumn + token.FullMatchedLength - 1 }

type TokenisedLine = TokenisedLine of tokens:FSharpTokenInfo list * stateAtEOL:int64

module Lexer =
    let inline isNotNull v = not (isNull v)

    let getLines (str: string) =
        use reader = new StringReader(str)
        [|
            let line = ref (reader.ReadLine())
            while isNotNull (!line) do
                yield !line
                line := reader.ReadLine()
            if str.EndsWith("\n") then
                // last trailing space not returned
                // http://stackoverflow.com/questions/19365404/stringreader-omits-trailing-linebreak
                yield String.Empty
        |]
    /// Get the array of all lex states in current source
    let internal getLexStates defines (source: string) =
        [|
            /// Iterate through the whole line to get the final lex state
            let rec loop (lineTokenizer: FSharpLineTokenizer) lexState =
                match lineTokenizer.ScanToken lexState with
                | None, newLexState -> newLexState
                | Some _, newLexState ->
                    loop lineTokenizer newLexState

            let sourceTokenizer = SourceTokenizer(defines, Some "/tmp.fsx")
            let lines = getLines source
            let mutable lexState = 0L
            for line in lines do
                yield lexState
                let lineTokenizer = sourceTokenizer.CreateLineTokenizer line
                lexState <- loop lineTokenizer lexState
        |]

    /// Provide a default implementation where we cache lex states of the current document.
    /// Assume that current document will be queried repeatedly
    /// Note: The source and defines are equality checked whenever this function is used which
    /// means that currentDocumentState is rebuilt whenever a different source or defines list is presented
    let queryLexState =
        let mutable currentDocumentState = ref None
        fun source defines line ->
            let lexStates =
                match !currentDocumentState with
                | Some (lexStates, s, d) when s = source && d = defines ->
                    lexStates
                // OPTIMIZE: if the new document has the current document as a prefix,
                // we can reuse lexing results and process only the added part.
                | _ ->
                    //LoggingService.LogDebug "queryLexState: lexing current document"
                    let lexStates = getLexStates defines source
                    currentDocumentState := Some (lexStates, source, defines)
                    lexStates
            Debug.Assert(line >= 0 && line < Array.length lexStates, "Should have lex states for every line.")
            lexStates.[line]

    let singleLineQueryLexState _ _ _ = 0L

    /// Return all tokens of current line
    let tokenizeLine source (args: string[]) line lineStr queryLexState =
        let defines =
            args |> Seq.choose (fun s -> if s.StartsWith "--define:" then Some s.[9..] else None)
                 |> Seq.toList
        let sourceTokenizer = SourceTokenizer(defines, Some "/tmp.fsx")
        let lineTokenizer = sourceTokenizer.CreateLineTokenizer lineStr
        let rec loop lexState acc =
            match lineTokenizer.ScanToken lexState with
            | Some tok, state -> loop state (tok :: acc)
            | _ -> List.rev acc
        loop (queryLexState source defines line) []

    let inline isIdentifier t = t.CharClass = FSharpTokenCharKind.Identifier
    let inline isOperator t = t.ColorClass = FSharpTokenColorKind.Operator
    let inline isKeyword t = t.ColorClass = FSharpTokenColorKind.Keyword

    let inline internal (|GenericTypeParameterPrefix|StaticallyResolvedTypeParameterPrefix|ActivePattern|Other|) ((token: FSharpTokenInfo), (lineStr:string)) =
        if token.Tag = FSharpTokenTag.QUOTE then GenericTypeParameterPrefix
        elif token.Tag = FSharpTokenTag.INFIX_AT_HAT_OP then
             // The lexer return INFIX_AT_HAT_OP token for both "^" and "@" symbols.
             // We have to check the char itself to distinguish one from another.
             if token.FullMatchedLength = 1 && lineStr.[token.LeftColumn] = '^' then
                StaticallyResolvedTypeParameterPrefix
             else Other
        elif token.Tag = FSharpTokenTag.LPAREN then
            if token.FullMatchedLength = 1 && lineStr.[token.LeftColumn+1] = '|' then
               ActivePattern
            else Other
        else Other

    // Operators: Filter out overlapped operators (>>= operator is tokenized as three distinct tokens: GREATER, GREATER, EQUALS.
    // Each of them has FullMatchedLength = 3. So, we take the first GREATER and skip the other two).
    //
    // Generic type parameters: we convert QUOTE + IDENT tokens into single IDENT token, altering its LeftColumn
    // and FullMathedLength (for "'type" which is tokenized as (QUOTE, left=2) + (IDENT, left=3, length=4)
    // we'll get (IDENT, left=2, length=5).
    //
    // Statically resolved type parameters: we convert INFIX_AT_HAT_OP + IDENT tokens into single IDENT token, altering its LeftColumn
    // and FullMathedLength (for "^type" which is tokenized as (INFIX_AT_HAT_OP, left=2) + (IDENT, left=3, length=4)
    // we'll get (IDENT, left=2, length=5).
    let internal fixTokens lineStr (tokens : FSharpTokenInfo list) =
        tokens
        |> List.fold (fun (acc, lastToken) token ->
            match lastToken with
            | Some t when token.LeftColumn <= t.RightColumn ->
                acc, lastToken
            | Some ( {Kind = SymbolKind.ActivePattern} as lastToken) when token.Tag = FSharpTokenTag.BAR || token.Tag = FSharpTokenTag.IDENT || token.Tag = FSharpTokenTag.UNDERSCORE ->
                let mergedToken =
                    {lastToken.Token with Tag = FSharpTokenTag.IDENT
                                                RightColumn = token.RightColumn
                                                FullMatchedLength = lastToken.Token.FullMatchedLength + token.FullMatchedLength }

                acc, Some { lastToken with Token = mergedToken; RightColumn = lastToken.RightColumn + token.FullMatchedLength }
            | _ ->
                match token, lineStr with
                | GenericTypeParameterPrefix -> acc, Some (DraftToken.Create GenericTypeParameter token)
                | StaticallyResolvedTypeParameterPrefix -> acc, Some (DraftToken.Create StaticallyResolvedTypeParameter token)
                | ActivePattern -> acc, Some (DraftToken.Create ActivePattern token)
                | Other ->
                    let draftToken =
                        match lastToken with
                        | Some { Kind = GenericTypeParameter | StaticallyResolvedTypeParameter as kind } when isIdentifier token ->
                              DraftToken.Create kind { token with LeftColumn = token.LeftColumn - 1
                                                                  FullMatchedLength = token.FullMatchedLength + 1 }
                        | Some ( { Kind = SymbolKind.ActivePattern } as ap) when token.Tag = FSharpTokenTag.RPAREN ->
                              DraftToken.Create SymbolKind.Ident ap.Token
                        | _ ->
                            let kind = 
                                if isOperator token then Operator 
                                elif isIdentifier token then Ident 
                                elif isKeyword token then Keyword
                                else Other
                            DraftToken.Create kind token
                    draftToken :: acc, Some draftToken
            ) ([], None)
        |> fst


    let getTokensWithInitialState state lines filename defines =
        [ let mutable state = state
          let sourceTok = SourceTokenizer(defines, filename)
          for lineText in lines do
              let tokenizer = sourceTok.CreateLineTokenizer(lineText)
              let rec parseLine() =
                  [ match tokenizer.ScanToken(state) with
                    | Some(tok), nstate ->
                        state <- nstate
                        yield tok
                        yield! parseLine()
                    | None, nstate -> state <- nstate ]
              yield parseLine(), state ]

    let findTokenAt col (tokens:FSharpTokenInfo list) =
        let isTokenAtOffset col (t:FSharpTokenInfo) = col-1 >= t.LeftColumn && col-1 <= t.RightColumn
        tokens |> List.tryFindBack (isTokenAtOffset col)

    let isNonTipToken token =
        token.ColorClass = FSharpTokenColorKind.Comment || token.ColorClass = FSharpTokenColorKind.String ||
                        (*token.ColorClass = FSharpTokenColorKind.Text ||*) token.ColorClass = FSharpTokenColorKind.InactiveCode

    // Returns symbol at a given position.
    let getSymbolFromTokens (tokens: FSharpTokenInfo list) line col (lineStr: string) lookupKind: LexerSymbol option =
        let tokens = fixTokens lineStr tokens

        // One or two tokens that in touch with the cursor (for "let x|(g) = ()" the tokens will be "x" and "(")
        let tokensUnderCursor =
            match lookupKind with
            | SymbolLookupKind.Simple | SymbolLookupKind.Fuzzy ->
                tokens |> List.filter (fun x -> x.Token.LeftColumn <= col && x.RightColumn + 1 >= col)
            | SymbolLookupKind.ByRightColumn ->
                tokens |> List.filter (fun x -> x.RightColumn = col)
            | SymbolLookupKind.ByLongIdent ->
                tokens |> List.filter (fun x -> x.Token.LeftColumn <= col)

        let inline orTry f =
            function
            | Some x -> Some x
            | None -> f()

        //printfn "Filtered tokens: %+A" tokensUnderCursor
        match lookupKind with
        | SymbolLookupKind.ByLongIdent ->
            // Try to find start column of the long identifiers
            // Assume that tokens are ordered in an decreasing order of start columns
            let rec tryFindStartColumn tokens =
               match tokens with
               | {Kind = Ident; Token = t1} :: {Kind = Operator; Token = t2} :: remainingTokens ->
                    if t2.Tag = FSharpTokenTag.DOT then
                        tryFindStartColumn remainingTokens
                    else
                        Some t1.LeftColumn
               | {Kind = Ident; Token = t} :: _ ->
                   Some t.LeftColumn
               | _ :: _ | [] ->
                   None
            let decreasingTokens =
                match tokensUnderCursor |> List.sortBy (fun token -> - token.Token.LeftColumn) with
                // Skip the first dot if it is the start of the identifier
                | {Kind = Operator; Token = t} :: remainingTokens when t.Tag = FSharpTokenTag.DOT ->
                    remainingTokens
                | newTokens -> newTokens

            match decreasingTokens with
            | [] -> None
            | first :: _ ->
                tryFindStartColumn decreasingTokens
                |> Option.map (fun leftCol ->
                    { Kind = Ident
                      Line = line
                      LeftColumn = leftCol
                      RightColumn = first.RightColumn + 1
                      Text = lineStr.[leftCol..first.RightColumn] })
        | SymbolLookupKind.Fuzzy
        | SymbolLookupKind.ByRightColumn ->
            // Select IDENT token. If failed, select OPERATOR token.
            tokensUnderCursor
            |> List.tryFind (fun { DraftToken.Kind = k } ->
                match k with
                | Ident | GenericTypeParameter | StaticallyResolvedTypeParameter | Keyword -> true
                | _ -> false)
                /// Gets the option if Some x, otherwise try to get another value

            |> orTry (fun _ -> tokensUnderCursor |> List.tryFind (fun { DraftToken.Kind = k } -> k = Operator))
            |> Option.map (fun token ->
                { Kind = token.Kind
                  Line = line
                  LeftColumn = token.Token.LeftColumn
                  RightColumn = token.RightColumn + 1
                  Text = lineStr.Substring(token.Token.LeftColumn, token.Token.FullMatchedLength) })
        | SymbolLookupKind.Simple ->
            tokensUnderCursor
            |> List.tryLast
            |> Option.map (fun token ->
                { Kind = token.Kind
                  Line = line
                  LeftColumn = token.Token.LeftColumn
                  RightColumn = token.RightColumn + 1
                  Text = lineStr.Substring(token.Token.LeftColumn, token.Token.FullMatchedLength) })

    let getSymbol source line col lineStr lookupKind (args: string[]) queryLexState =
        let tokens = tokenizeLine source args line lineStr queryLexState
        try
            getSymbolFromTokens tokens line col lineStr lookupKind
        with e ->
            //LoggingService.LogInfo (sprintf "Getting lex symbols failed with %O" e)
            None

    module Comments =
        open Microsoft.FSharp.Compiler.SourceCodeServices

        type LineCommentInfo =
            | WholeLine of wraps:bool
            | Range of left:int * right:int * wraps:bool
            | Line of left:int * wraps:bool

        type LineComment =
            { Line : int
              Comment : LineCommentInfo }

        module Impl =
            let collectTokens initialState (lineTokenizer:FSharpLineTokenizer) =
                let rec loop state (currentState,tokens) =
                    match lineTokenizer.ScanToken state with
                    | Some tok, nextState ->
                        loop nextState (nextState,(tok::tokens)) 
                    | None, nextState ->
                        nextState,tokens
        
                let finalState,tokensRev = loop initialState (0L,[])

                finalState,tokensRev |> List.rev

            let tokenizeText (sourceTokenizer:FSharpSourceTokenizer) sourceCodeLines =
                let rec loop lines state acc =
                    match lines with
                    | line::restLines ->
                        let (latestState,lineTokens) =
                            line 
                            |> sourceTokenizer.CreateLineTokenizer
                            |> collectTokens state
                        loop restLines latestState ((line,lineTokens)::acc)
                    | [] ->
                        acc

                loop sourceCodeLines 0L []
                |> List.rev
                |> List.mapi (fun i (line,tokens) -> i,tokens)

            let aggregateCommentTokens (tokens:FSharpTokenInfo list) = 
                let rec foldCommentTokens (foldedToken:FSharpTokenInfo) (tokensLeft:FSharpTokenInfo list) =
                    match tokensLeft with
                    | [] -> 
                        foldedToken,tokensLeft
                    | t::ts ->
                        let isSameTokenKind = 
                            t.ColorClass = FSharpTokenColorKind.Comment && t.CharClass = foldedToken.CharClass
                        if isSameTokenKind then
                            foldCommentTokens { foldedToken with 
                                                    RightColumn = t.RightColumn
                                                    FullMatchedLength = t.RightColumn - foldedToken.LeftColumn + 1 } ts
                        else
                            foldedToken,t::ts
                
                let rec loop acc (tokensLeft:FSharpTokenInfo list) =
                    match tokensLeft with
                    | [] -> 
                        acc
                    | t::ts when t.ColorClass <> FSharpTokenColorKind.Comment ->
                        loop (t::acc) ts
                    | t::ts ->
                        let (foldedToken,rest) = foldCommentTokens t ts
                        loop (foldedToken::acc) rest

                loop [] tokens |> List.rev

            let isComment (token:FSharpTokenInfo) =
                token.ColorClass = FSharpTokenColorKind.Comment

            let isNotComment = isComment >> not

            let isLineComment (token:FSharpTokenInfo) =
                token.CharClass = FSharpTokenCharKind.LineComment

            let isRangeComment (token:FSharpTokenInfo) =
                token.CharClass = FSharpTokenCharKind.Comment

            let getComments (linesTokens:(int*FSharpTokenInfo list) list) =
                let commentsRanges =
                    linesTokens
                    |> List.map (fun (line,tokens) -> 
                        line,tokens |> aggregateCommentTokens)
                    |> List.collect (fun (l,toks) ->
                        match toks with
                        | [] -> 
                            [l,None]
                        | _ -> 
                            toks |> List.map (fun tok -> l,tok |> Some))

                commentsRanges
                |> List.fold (fun comments (line,currToken) ->
                    match currToken, comments |> List.tryHead with
                    | None, None ->
                        comments
                    | None, Some prevComment ->
                        let updatedComments =
                            match prevComment.Comment with
                            | LineCommentInfo.Line (_,true) | LineCommentInfo.WholeLine true | LineCommentInfo.Range (_,_,true) -> 
                                { prevComment with Comment = LineCommentInfo.WholeLine true }::(comments |> List.skip 1)
                            | _ -> 
                                comments
                        { Line = line; Comment = LineCommentInfo.WholeLine true }::updatedComments
                    | Some token, None ->
                        if token |> isNotComment then
                            comments
                        else
                            let comment =
                                if token |> isLineComment then
                                    if token.LeftColumn = 0 then { Line = line; Comment = LineCommentInfo.WholeLine false }
                                    else { Line = line; Comment = LineCommentInfo.Line (token.LeftColumn,false) }
                                else
                                    { Line = line; Comment = LineCommentInfo.Range (token.LeftColumn,token.RightColumn,true) }
                            comment::comments
                    | Some token, Some prevComment ->
                        if token |> isRangeComment then
                            let updatedComments = 
                                match prevComment.Comment with
                                | LineCommentInfo.Range (left,_,true) when line <> prevComment.Line ->
                                    if left = 0 then 
                                        { prevComment with Comment = LineCommentInfo.WholeLine true }::(comments |> List.skip 1)
                                    else
                                        { prevComment with Comment = LineCommentInfo.Line (left,true) }::(comments |> List.skip 1)
                                | LineCommentInfo.Line (left,true) when line <> prevComment.Line ->
                                    if left = 0 then 
                                        { prevComment with Comment = LineCommentInfo.WholeLine true }::(comments |> List.skip 1)
                                    else
                                        { prevComment with Comment = LineCommentInfo.Line (left,true) }::(comments |> List.skip 1)
                                | LineCommentInfo.WholeLine true when line <> prevComment.Line ->
                                    { prevComment with Comment = LineCommentInfo.WholeLine true }::(comments |> List.skip 1)
                                | _ -> 
                                    comments
                            { Line = line; Comment = LineCommentInfo.Range (token.LeftColumn,token.RightColumn,true) }::updatedComments
                        elif token |> isNotComment then
                            match prevComment.Comment with
                            | LineCommentInfo.Range (left,right,true) ->
                                { prevComment with Comment = LineCommentInfo.Range (left,right,false) }::(comments |> List.skip 1)
                            | _ ->
                                comments
                        else
                            if token |> isLineComment then
                                let comment =
                                    if token.LeftColumn = 0 then
                                        { Line = line; Comment = LineCommentInfo.WholeLine false }
                                    else
                                        { Line = line; Comment = LineCommentInfo.Line (token.LeftColumn,false) }
                                comment::comments
                            else
                                comments
                    ) []
                |> List.rev

        let getComments text =
            let sourceTokenizer = FSharpSourceTokenizer ([], None)

            text
            |> getLines
            |> List.ofArray
            |> Impl.tokenizeText sourceTokenizer
            |> Impl.getComments