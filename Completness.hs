-- check for completeness of size patterns
module Completness (completePatterns) where

import Abstract

-- Inductive functions must not match on successor size patterns ($ p)
-- (Thesis Fig. 5.7). Dot patterns .($ i) are DotP, not SuccP, and are allowed.
completePatterns :: [Clause] -> Bool
completePatterns cl = all completeClause cl

completeClause :: Clause -> Bool
completeClause (Clause pl _) = all cp pl

cp :: Pattern -> Bool
cp (SuccP _) = False
cp (ConP _ _ pl) = all cp pl
cp _ = True
