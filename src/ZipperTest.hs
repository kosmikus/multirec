{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ZipperTest where

import Prelude hiding (exp)

import Data.Maybe

import AST
import Base
import ShowFam
import ZigZag
import Zipper

-------------------------------------------------------------------------------
-- traversing the left spine of a Zig and printing all subtrees encountered
-------------------------------------------------------------------------------

printLeftSpine :: (ShowFam l, Zipper l ix) => l ix -> ix -> IO ()
printLeftSpine ix = go ix . enter
  where
    go :: ShowFam l => l ix -> Loc l ix -> IO ()
    go ix loc = printFam `on` loc >> maybe (return ()) (go ix) (down loc)

-------------------------------------------------------------------------------
-- test
-------------------------------------------------------------------------------

instance Zipper ZigZag Zig

zig :: Zig
zig = Zig (Zag (Zig Zap))

test1 :: IO ()
test1 =  printLeftSpine ZZig zig

instance Zipper AST Exp

locExp :: Loc AST Exp
locExp = enter $ Let ("id" := Abs "x" (Var "x")) (App (Var "id") (Var "y"))

test2 :: IO ()
test2 =  printLeftSpine Exp (leave locExp)

test3 :: IO ()
test3 =  printFam `on` fromJust (walk locExp) 
  where
    walk e = down e >>= right >>= left >>= down >>= up >>= down

test4 :: Exp
test4 =  leave . update upd . fromJust $ down' locExp >>= down'
  where
    upd :: AST ix -> ix -> ix
    upd Exp _ = Var "z"