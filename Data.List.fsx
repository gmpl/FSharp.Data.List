let flip f x y = f y x
let const' k _ = k
let (++) = (@)

module List =

    // -----------------------------------------------------------------------------
    // -- |
    // -- Module      :  Data.List
    // -- Copyright   :  (c) The University of Glasgow 2001
    // -- License     :  BSD-style (see the file libraries/base/LICENSE)
    // --
    // -- Maintainer  :  libraries@haskell.org
    // -- Stability   :  stable
    // -- Portability :  portable
    // --
    // -- Operations on lists.
    // --
    // -----------------------------------------------------------------------------



    ///  'span', applied to a predicate @p@ and a list @xs@, returns a tuple where
    /// first element is longest prefix (possibly empty) of @xs@ of elements that
    /// satisfy @p@ and second element is the remainder of the list:
    /// 
    ///  span (< 3) [1,2,3,4,1,2,3,4] == ([1,2],[3,4,1,2,3,4])
    ///  span (< 9) [1,2,3] == ([1,2,3],[])
    ///  span (< 0) [1,2,3] == ([],[1,2,3])
    /// 
    /// span' @p xs@ is equivalent to @('takeWhile' p xs, 'dropWhile' p xs)@
    let rec span a b =
        match a, b with 
        | _, (  []     as xs) -> xs, xs
        | p, ((x::xs') as xs) ->
                if  p x then let ys, zs = span p xs' in (x::ys, zs)
                else [], xs

    /// Not exported:
    /// We want to make every element in the 'intersperse'd list available
    /// as soon as possible to avoid space leaks. Experiments suggested that
    /// a separate top-level helper is more efficient than a local worker.
    let rec prependToAll a b =
        match a, b with     
        | _  , []    -> []
        | sep, x::xs -> sep :: x :: prependToAll sep xs

    /// The 'intersperse' function takes an element and a list and 'intersperses' that element between the elements of the list.
    /// For example,
    ///
    /// > intersperse ',' "abcde" == "a,b,c,d,e"
    let intersperse a b =
        match a, b with
        | _  , []    -> []
        | sep, x::xs -> x :: prependToAll sep xs



    /// 'intercalate' @xs xss@ is equivalent to @('concat' ('intersperse' xs xss))@.
    /// It inserts the list @xs@ in between the lists in @xss@ and concatenates the
    /// result.
    let intercalate xs xss = List.concat (intersperse xs xss)






    // -----------------------------------------------------------------------------
    // -- |
    // -- Module      :  Data.List.Split.Internals
    // -- Copyright   :  (c) Brent Yorgey, Louis Wasserman 2008-2012
    // -- License     :  BSD-style (see LICENSE)
    // -- Maintainer  :  Brent Yorgey <byorgey@gmail.com>
    // -- Stability   :  stable
    // -- Portability :  Haskell 2010
    // --
    // -- Implementation module for "Data.List.Split", a combinator library
    // -- for splitting lists.  See the "Data.List.Split" documentation for
    // -- more description and examples.
    // --
    // -----------------------------------------------------------------------------

    /// A delimiter is a list of predicates on elements, matched by some contiguous subsequence of a list.
    type Delimiter<'a> = Delimiter of ('a -> bool) list

    /// Try to match a delimiter at the start of a list, either failing
    /// or decomposing the list into the portion which matched the delimiter
    /// and the remainder.
    let rec matchDelim a b = 
        match a, b with
        | Delimiter []     , xs    -> Some ([], xs)
        | Delimiter _      , []    -> None
        | Delimiter (p::ps), x::xs ->
            let (>>=) lst f = Option.bind f lst
            if p x then matchDelim (Delimiter ps) xs >>= fun (h, t) -> Some (x::h, t)
            else None

    /// What to do with delimiters?
    type DelimPolicy = 

        /// Drop delimiters from the output.
        | Drop
    
        /// Keep delimiters as separate chunks of the output.
        | Keep

        /// Keep delimiters in the output, prepending them to the following chunk.
        | KeepLeft

        /// Keep delimiters in the output, appending them to the previous chunk.
        | KeepRight

    /// What to do with multiple consecutive delimiters?
    type CondensePolicy = 

        /// Condense into a single delimiter.
        | Condense         
    
        /// Keep consecutive
        /// delimiters separate, but
        /// don't insert blank chunks in
        /// between them.
        | DropBlankFields                       
                       
        /// Insert blank chunks
        /// between consecutive
        /// delimiters.
        | KeepBlankFields

    type EndPolicy = DropBlank | KeepBlank

    /// A splitting strategy.
    type Splitter<'a> = {
     
            /// What delimiter to split on
            delimiter   : Delimiter<'a>  

            /// What to do with delimiters (drop from output, keep as separate elements in output, or merge with previous or following chunks)
            delimPolicy : DelimPolicy
                               
            /// What to do with multiple consecutive delimiters
            condensePolicy : CondensePolicy 

            /// Drop an initial blank?
            initBlankPolicy  : EndPolicy

            /// Drop a final blank?
            finalBlankPolicy : EndPolicy }


    ///   The default splitting strategy: keep delimiters in the output
    ///   as separate chunks, don't condense multiple consecutive
    ///   delimiters into one, keep initial and final blank chunks.
    ///   Default delimiter is the constantly false predicate.
    ///
    ///   Note that 'defaultSplitter' should normally not be used; use
    ///   'oneOf', 'onSublist', or 'whenElt' instead, which are the same as
    ///   the 'defaultSplitter' with just the delimiter overridden.
    ///
    ///   The 'defaultSplitter' strategy with any delimiter gives a
    ///   maximally information-preserving splitting strategy, in the sense
    ///   that (a) taking the 'concat' of the output yields the original
    ///   list, and (b) given only the output list, we can reconstruct a
    ///   'Splitter' which would produce the same output list again given
    ///   the original input list.  This default strategy can be overridden
    ///   to allow discarding various sorts of information.
    let defaultSplitter<'a> : Splitter<'a> =
        let const' k _ = k
        {          
            delimiter        = Delimiter [const' false]
            delimPolicy      = Keep
            condensePolicy   = KeepBlankFields
            initBlankPolicy  = KeepBlank
            finalBlankPolicy = KeepBlank
        }

    /// Tag chunks as delimiters or text.
    type Chunk<'a> = Delim of 'a list | Text of 'a list

    /// Internal representation of a split list that tracks which pieces
    /// are delimiters and which aren't.
    type SplitList<'a> = Chunk<'a> list

    ///Untag a 'Chunk'.
    let fromElem = function
        | Text  a -> a
        | Delim a -> a

    /// Test whether a 'Chunk' is a delimiter.
    let isDelim = function
        | Delim _ -> true
        | _       -> false


        

    let rec breakDelim a b =
        match a, b with
        | Delimiter [], xs               -> [], Some ([], xs)
        | _           , []               -> [], None
        | d           , ((x::xs) as xxs) ->
            match matchDelim d xxs with
            | None      -> let ys, mtch = breakDelim d xs in (x::ys, mtch)
            | Some mtch -> [], Some mtch


    /// Given a delimiter to use, split a list into an internal
    /// representation with chunks tagged as delimiters or text.  This
    /// transformation is lossless; in particular,
    ///
    ///
    /// 'concatMap' 'fromElem' ('splitInternal' d l) == l.
    ///
    let rec splitInternal a b =
        let toSplitList d = function
            | None               -> []
            | Some ([], r::rs)   -> Delim [] :: Text [r] :: splitInternal d rs
            | Some (delim, rest) -> Delim delim :: splitInternal d rest

        match a, b with
        | _, []  -> []
        | d, xxs ->
            let xs, mtch = breakDelim d xxs
            if List.isEmpty xs then toSplitList d mtch
            else Text xs :: toSplitList d mtch

    /// Drop an initial blank chunk according to the given 'EndPolicy'.
    let dropInitial a b =
        match a, b with
        | DropBlank, Text [] :: l -> l
        | _        , l            -> l

    /// Drop a final blank chunk according to the given 'EndPolicy'.
    let dropFinal a b =
        let rec dropFinal' = function
            | []        -> []
            | [Text []] -> []
            | x :: xs   -> x::dropFinal' xs
        match a, b with
        | _        , [] -> []
        | DropBlank, l  -> dropFinal' l
        | _        , l  -> l

    /// Merge delimiters with adjacent chunks to the right (yes, that's
    ///   not a typo: the delimiters should end up on the left of the
    ///   chunks, so they are merged with chunks to their right).
    let rec mergeLeft = function
        | []                     -> []
        | Delim d :: Text c :: l -> Text (d ++ c) :: mergeLeft l
        | c :: l                 -> c :: mergeLeft l

    /// Merge delimiters with adjacent chunks to the left.
    let rec mergeRight = function
        | [] -> []
    // below fanciness is with the goal of laziness: we want to start returning
    // stuff before we've necessarily discovered a delimiter, in case we're
    // processing some infinite list with no delimiter
        | Text c :: l -> 
            let d, lTail = 
                match l with
                | Delim d' :: l' -> d', l'
                | _              -> [], l
            Text (c ++ d) :: mergeRight lTail
        | c :: l -> c :: mergeRight l

    /// Merge delimiters into adjacent chunks according to the 'DelimPolicy'.
    let doMerge = function
        | KeepLeft  -> mergeLeft
        | KeepRight -> mergeRight
        | _         -> id

    /// Drop delimiters if the 'DelimPolicy' is 'Drop'.
    let doDrop a b =
        match a, b with
        | Drop, l -> [for c in l do match c with (Text _) -> yield c | _ -> ()]
        | _   , l -> l

    /// Condense multiple consecutive delimiters into one if the
    /// 'CondensePolicy' is 'Condense'.
    let doCondense a b =
        match a, b with
        | Condense, ls -> 
            let rec condense' = function
                | [] -> []
                | ((Text _) as c :: l) -> c :: condense' l
                | l -> 
                    let ds, rest = span isDelim l
                    (Delim <| List.collect fromElem ds) :: condense' rest
            condense' ls
        | _, ls -> ls

    /// Insert blank chunks between consecutive delimiters.
    let rec insertBlanks' a b =
        match a, b with
        | _, [] -> []
        | DropBlankFields as cp, (Delim _ as d1) :: (Delim _ as d2) :: l
          -> d1           :: insertBlanks' cp (d2::l)
        | cp, (Delim _ as d1) :: (Delim _ as d2) :: l
          -> d1 :: Text [] :: insertBlanks' cp (d2::l)
        | _, [Delim _ as d] -> [d; Text []]
        | cp, c :: l -> c :: insertBlanks' cp l

    /// Insert blank chunks between any remaining consecutive delimiters
    /// (unless the condense policy is 'DropBlankFields'), and at the
    /// beginning or end if the first or last element is a delimiter.
    let insertBlanks a b =
        match a, b with
        | _ , []                  -> [Text []]
        | cp, (Delim _ as d :: l) -> Text [] :: insertBlanks' cp (d::l)
        | cp, l                   -> insertBlanks' cp l

    /// Given a split list in the internal tagged representation, produce
    /// a new internal tagged representation corresponding to the final
    /// output, according to the strategy defined by the given 'Splitter'.
    let postProcess (s:Splitter<_>) =
        dropFinal s.finalBlankPolicy
            << dropInitial s.initBlankPolicy
            << doMerge s.delimPolicy
            << doDrop  s.delimPolicy
            << insertBlanks s.condensePolicy
            << doCondense   s.condensePolicy


    

    // * Combinators

    /// Split a list according to the given splitting strategy.  This is
    /// how to \"run\" a 'Splitter' that has been built using the other
    /// combinators.
    let split s = List.map fromElem << postProcess s << splitInternal s.delimiter




    // ** Basic strategies
    //
    // $ All these basic strategies have the same parameters as the
    // 'defaultSplitter' except for the delimiters.
    
    /// A splitting strategy that splits on any one of the given
    ///   elements.  For example:
    ///
    /// > split (oneOf "xyz") "aazbxyzcxd" == ["aa","z","b","x","","y","","z","c","x","d"]
    let oneOf elts = {defaultSplitter with delimiter = Delimiter [(flip List.contains elts)]}

    /// A splitting strategy that splits on the given list, when it is
    ///   encountered as an exact subsequence.  For example:
    ///
    /// > split (onSublist "xyz") "aazbxyzcxd" == ["aazb","xyz","cxd"]
    ///
    ///   Note that splitting on the empty list is a special case, which
    ///   splits just before every element of the list being split.  For example:
    ///
    /// > split (onSublist "") "abc" == ["","","a","","b","","c"]
    /// > split (dropDelims . dropBlanks $ onSublist "") "abc" == ["a","b","c"]
    ///
    ///   However, if you want to break a list into singleton elements like
    ///   this, you are better off using @'chunksOf' 1@, or better yet,
    ///   @'map' (:[])@.
    let onSublist lst = {defaultSplitter with delimiter = Delimiter (List.map (=) lst)}

    /// A splitting strategy that splits on any elements that satisfy the
    /// given predicate.  For example:
    ///
    /// > split (whenElt (<0)) [2,4,-3,6,-9,1] == [[2,4],[-3],[6],[-9],[1]]
    let whenElt p = {defaultSplitter with delimiter = Delimiter [p]}




    // Strategy transformers

    /// Drop delimiters from the output (the default is to keep
    ///  them). For example,
    ///
    /// > split (oneOf ":") "a:b:c" == ["a", ":", "b", ":", "c"]
    /// > split (dropDelims $ oneOf ":") "a:b:c" == ["a", "b", "c"]
    let dropDelims s = {s with delimPolicy = Drop}

    /// Condense multiple consecutive delimiters into one.  For example:
    ///
    /// > split (condense $ oneOf "xyz") "aazbxyzcxd" == ["aa","z","b","xyz","c","x","d"]
    /// > split (dropDelims $ oneOf "xyz") "aazbxyzcxd" == ["aa","b","","","c","d"]
    /// > split (condense . dropDelims $ oneOf "xyz") "aazbxyzcxd" == ["aa","b","c","d"]
    let condense s = {s with condensePolicy = Condense}

    /// Don't generate a blank chunk if there is a delimiter at the
    /// beginning.  For example:
    ///
    /// > split (oneOf ":") ":a:b" == ["",":","a",":","b"]
    /// > split (dropInitBlank $ oneOf ":") ":a:b" == [":","a",":","b"]
    let dropInitBlank s = {s with initBlankPolicy = DropBlank}

    /// Don't generate a blank chunk if there is a delimiter at the end.
    /// For example:
    ///
    /// > split (oneOf ":") "a:b:" == ["a",":","b",":",""]
    /// > split (dropFinalBlank $ oneOf ":") "a:b:" == ["a",":","b",":"]
    let dropFinalBlank s = {s with finalBlankPolicy = DropBlank}

    /// Don't generate blank chunks between consecutive delimiters.
    /// For example:
    ///
    /// > split (oneOf ":") "::b:::a" == ["",":","",":","b",":","",":","",":","a"]
    /// > split (dropInnerBlanks $ oneOf ":") "::b:::a" == ["", ":",":","b",":",":",":","a"]
    let dropInnerBlanks s = {s with condensePolicy = DropBlankFields}




    // ** Derived combinators

    /// Drop all blank chunks from the output, and condense consecutive
    /// delimiters into one.  Equivalent to @'dropInitBlank'
    /// . 'dropFinalBlank' . 'condense'@.  For example:
    ///
    /// > split (oneOf ":") "::b:::a" == ["",":","",":","b",":","",":","",":","a"]
    /// > split (dropBlanks $ oneOf ":") "::b:::a" == ["::","b",":::","a"]
    let dropBlanks x = (dropInitBlank << dropFinalBlank << condense) x




    // ** Convenience functions
    //
    // These functions implement some common splitting strategies.  Note
    // that all of the functions in this section drop delimiters from
    // the final output, since that is a more common use case even
    // though it is not the default.

    /// Split on any of the given elements.  Equivalent to @'split'
    /// . 'dropDelims' . 'oneOf'@.  For example:
    ///
    /// > splitOneOf ";.," "foo,bar;baz.glurk" == ["foo","bar","baz","glurk"]
    let splitOneOf x = (split << dropDelims << oneOf) x


    /// @'splitOn' x . 'Data.List.intercalate' x@ is the identity on
    /// certain lists, but it is tricky to state the precise conditions
    /// under which this holds.  (For example, it is not enough to say
    /// that @x@ does not occur in any elements of the input list.
    /// Working out why is left as an exercise for the reader.)
    let splitOn x = (split << dropDelims << onSublist) x

    /// Split on elements satisfying the given predicate.  Equivalent to
    /// @'split' . 'dropDelims' . 'whenElt'@.  For example:
    ///
    /// > splitWhen (<0) [1,3,-4,5,7,-9,0,2] == [[1,3],[5,7],[0,2]]    
    let splitWhen x = (split << dropDelims << whenElt) x