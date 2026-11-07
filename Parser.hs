module Parser (parse) where

import qualified Lexer as T
import qualified Concrete as C
import qualified Abstract as A
import Abstract (Name)

parse :: [T.Token] -> [C.Declaration]
parse ts =
  case parseDeclarations ts of
    (decls, []) -> decls
    (_, rest)   -> parseError rest

parseDeclarations :: [T.Token] -> ([C.Declaration], [T.Token])
parseDeclarations [] = ([], [])
parseDeclarations ts@(T.BrClose _ : _) = ([], ts)
parseDeclarations ts =
  let (d, ts1)  = parseDeclaration ts
      (ds, ts2) = parseDeclarations ts1
  in (d : ds, ts2)

parseDeclaration :: [T.Token] -> (C.Declaration, [T.Token])
parseDeclaration (T.Data _ : T.Id name _ : ts) =
  parseDataRest name A.NotSized A.Ind ts
parseDeclaration (T.Sized _ : T.Data _ : T.Id name _ : ts) =
  parseDataRest name A.Sized A.Ind ts
parseDeclaration (T.CoData _ : T.Id name _ : ts) =
  parseDataRest name A.NotSized A.CoInd ts
parseDeclaration (T.Sized _ : T.CoData _ : T.Id name _ : ts) =
  parseDataRest name A.Sized A.CoInd ts
parseDeclaration (T.Fun _ : ts) =
  let (tsig, ts1) = parseTypeSig ts
      ts2         = expectBrOpen ts1
      (cls, ts3)  = parseClauses ts2
      ts4         = expectBrClose ts3
  in (C.FunDecl A.Ind tsig cls, ts4)
parseDeclaration (T.CoFun _ : ts) =
  let (tsig, ts1) = parseTypeSig ts
      ts2         = expectBrOpen ts1
      (cls, ts3)  = parseClauses ts2
      ts4         = expectBrClose ts3
  in (C.FunDecl A.CoInd tsig cls, ts4)
parseDeclaration (T.Mutual _ : T.BrOpen _ : ts) =
  let (decls, ts1) = parseDeclarations ts
      ts2          = expectBrClose ts1
  in (C.MutualDecl decls, ts2)
parseDeclaration (T.Let _ : ts) =
  let (tsig, ts1) = parseTypeSig ts
      ts2         = expectEq ts1
      (e, ts3)    = parseExpr ts2
  in (C.LetDecl False tsig e, ts3)
parseDeclaration (T.Eval _ : T.Let _ : ts) =
  let (tsig, ts1) = parseTypeSig ts
      ts2         = expectEq ts1
      (e, ts3)    = parseExpr ts2
  in (C.LetDecl True tsig e, ts3)
parseDeclaration ts = parseError ts

parseDataRest :: Name -> A.Sized -> A.Co -> [T.Token] -> (C.Declaration, [T.Token])
parseDataRest name sz co ts =
  let (tel, ts1) = parseDataTelescope ts
      ts2        = expectCol ts1
      (ty, ts3)  = parseExpr ts2
      ts4        = expectBrOpen ts3
      (cs, ts5)  = parseConstructors ts4
      ts6        = expectBrClose ts5
  in (C.DataDecl name sz co tel ty cs, ts6)

parseDataTelescope :: [T.Token] -> (C.Telescope, [T.Token])
parseDataTelescope (T.PrOpen _ : T.Plus _ : T.Id x _ : T.Col _ : ts) =
  let (ty, ts1)  = parseExpr ts
      ts2        = expectPrClose ts1
      (tel, ts3) = parseDataTelescope ts2
  in (C.PosTB x ty : tel, ts3)
parseDataTelescope (T.PrOpen _ : T.Id x _ : T.Col _ : ts) =
  let (ty, ts1)  = parseExpr ts
      ts2        = expectPrClose ts1
      (tel, ts3) = parseDataTelescope ts2
  in (C.TB x ty : tel, ts3)
parseDataTelescope ts = ([], ts)

parseTypeSig :: [T.Token] -> (C.TypeSig, [T.Token])
parseTypeSig (T.Id name _ : T.Col _ : ts) =
  let (ty, ts1) = parseExpr ts
  in (C.TypeSig name ty, ts1)
parseTypeSig ts = parseError ts

parseConstructors :: [T.Token] -> ([C.Constructor], [T.Token])
parseConstructors ts@(T.BrClose _ : _) = ([], ts)
parseConstructors ts =
  let (c, ts1) = parseTypeSig ts
  in case ts1 of
       (T.Sem _ : ts2) ->
         let (cs, ts3) = parseConstructors ts2
         in (c : cs, ts3)
       _ -> ([c], ts1)

parseClauses :: [T.Token] -> ([C.Clause], [T.Token])
parseClauses ts@(T.BrClose _ : _) = ([], ts)
parseClauses ts =
  let (c, ts1) = parseClause ts
  in case ts1 of
       (T.Sem _ : ts2) ->
         let (cs, ts3) = parseClauses ts2
         in (c : cs, ts3)
       _ -> ([c], ts1)

parseClause :: [T.Token] -> (C.Clause, [T.Token])
parseClause (T.Id _ _ : ts) =
  let (ps, ts1) = parsePatternsUntilEq ts
      ts2       = expectEq ts1
      (rhs, ts3) = parseExpr ts2
  in (C.Clause ps rhs, ts3)
parseClause ts = parseError ts

parsePatternsUntilEq :: [T.Token] -> ([C.Pattern], [T.Token])
parsePatternsUntilEq ts@(T.Eq _ : _) = ([], ts)
parsePatternsUntilEq ts@(T.PrClose _ : _) = ([], ts)
parsePatternsUntilEq ts =
  let (p, ts1)  = parsePattern ts
      (ps, ts2) = parsePatternsUntilEq ts1
  in (p : ps, ts2)

parsePattern :: [T.Token] -> (C.Pattern, [T.Token])
parsePattern (T.PrOpen _ : T.Succ _ : ts) =
  let (sp, ts1) = parseSP ts
      ts2       = expectPrClose ts1
  in (C.SuccP sp, ts2)
parsePattern (T.PrOpen _ : T.Id c _ : ts) =
  let (ps, ts1) = parsePatternsUntilEq ts
      ts2       = expectPrClose ts1
  in (C.ConP c ps, ts2)
parsePattern (T.Id x _ : ts) = (C.IdentP x, ts)
parsePattern (T.Dot _ : ts) =
  let (e, ts1) = parseExpr3 ts
  in (C.DotP e, ts1)
parsePattern ts = parseError ts

parseSP :: [T.Token] -> (C.Pattern, [T.Token])
parseSP (T.Succ _ : ts) =
  let (sp, ts1) = parseSP ts
  in (C.SuccP sp, ts1)
parseSP ts = parsePattern ts

parseExpr :: [T.Token] -> (C.Expr, [T.Token])
parseExpr (T.Lam _ : T.Id x _ : T.Arrow _ : ts) =
  let (e, ts1) = parseExpr ts
  in (C.Lam x e, ts1)
parseExpr (T.Let _ : T.Id x _ : T.Col _ : ts) =
  let (ty, ts1) = parseExpr ts
      ts2       = expectEq ts1
      (e1, ts3) = parseExpr ts2
      ts4       = expectIn ts3
      (e2, ts5) = parseExpr ts4
  in (C.LLet x ty e1 e2, ts5)
parseExpr ts
  | Just (x, ty, tsAfterArrow) <- tryParseTArrow ts =
      let (body, ts1) = parseExpr tsAfterArrow
      in (C.Pi x ty body, ts1)
  | otherwise =
      let (e1, ts1) = parseExpr1 ts
      in case ts1 of
           (T.Arrow _ : ts2) ->
             let (e2, ts3) = parseExpr ts2
             in (C.Pi "" e1 e2, ts3)
           _ -> (e1, ts1)

tryParseTArrow :: [T.Token] -> Maybe (Name, C.Expr, [T.Token])
tryParseTArrow (T.PrOpen _ : T.Id x _ : T.Col _ : ts) =
  let (ty, ts1) = parseExpr ts
  in case ts1 of
       (T.PrClose _ : T.Arrow _ : ts2) -> Just (x, ty, ts2)
       _ -> Nothing
tryParseTArrow _ = Nothing

parseExpr1 :: [T.Token] -> (C.Expr, [T.Token])
parseExpr1 ts =
  let (es, ts1) = parseExpr2 ts
  in case es of
       [e]    -> (e, ts1)
       (e:el) -> (C.App e el, ts1)
       []     -> parseError ts

parseExpr2 :: [T.Token] -> ([C.Expr], [T.Token])
parseExpr2 (T.Succ _ : ts) =
  let (se, ts1)  = parseSE ts
      (rest, ts2) = parseExpr3Many ts1
  in (C.Succ se : rest, ts2)
parseExpr2 ts =
  let (e, ts1)    = parseExpr3 ts
      (rest, ts2) = parseExpr3Many ts1
  in (e : rest, ts2)

parseSE :: [T.Token] -> (C.Expr, [T.Token])
parseSE (T.Succ _ : ts) =
  let (se, ts1) = parseSE ts
  in (C.Succ se, ts1)
parseSE ts = parseExpr3 ts

parseExpr3Many :: [T.Token] -> ([C.Expr], [T.Token])
parseExpr3Many ts
  | startsExpr3 ts =
      let (e, ts1)  = parseExpr3 ts
          (es, ts2) = parseExpr3Many ts1
      in (e : es, ts2)
  | otherwise = ([], ts)

startsExpr3 :: [T.Token] -> Bool
startsExpr3 (T.Set _ : _)    = True
startsExpr3 (T.Size _ : _)   = True
startsExpr3 (T.Infty _ : _)  = True
startsExpr3 (T.Id _ _ : _)   = True
startsExpr3 (T.PrOpen _ : _) = True
startsExpr3 _                = False

parseExpr3 :: [T.Token] -> (C.Expr, [T.Token])
parseExpr3 (T.Set _ : ts)   = (C.Set, ts)
parseExpr3 (T.Size _ : ts)  = (C.Size, ts)
parseExpr3 (T.Infty _ : ts) = (C.Infty, ts)
parseExpr3 (T.Id x _ : ts)  = (C.Ident x, ts)
parseExpr3 (T.PrOpen _ : ts) =
  let (e, ts1) = parseExpr ts
      ts2      = expectPrClose ts1
  in (e, ts2)
parseExpr3 ts = parseError ts

expectBrOpen :: [T.Token] -> [T.Token]
expectBrOpen (T.BrOpen _ : ts) = ts
expectBrOpen ts = parseError ts

expectBrClose :: [T.Token] -> [T.Token]
expectBrClose (T.BrClose _ : ts) = ts
expectBrClose ts = parseError ts

expectPrClose :: [T.Token] -> [T.Token]
expectPrClose (T.PrClose _ : ts) = ts
expectPrClose ts = parseError ts

expectCol :: [T.Token] -> [T.Token]
expectCol (T.Col _ : ts) = ts
expectCol ts = parseError ts

expectEq :: [T.Token] -> [T.Token]
expectEq (T.Eq _ : ts) = ts
expectEq ts = parseError ts

expectIn :: [T.Token] -> [T.Token]
expectIn (T.In _ : ts) = ts
expectIn ts = parseError ts

parseError :: [T.Token] -> a
parseError [] = error "Parse error at EOF"
parseError (x : _) = error ("Parse error at token " ++ T.prettyTok x)
