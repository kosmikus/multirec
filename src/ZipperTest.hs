{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ZipperTest where

import Base
import ZigZag
import Zipper

-------------------------------------------------------------------------------
-- enable Zipper functionality for Zig and Zag
-------------------------------------------------------------------------------

instance Zipper ZigZag Zig
instance Zipper ZigZag Zag

-------------------------------------------------------------------------------
-- traversing the left spine of a Zig and printing all subtrees encountered
-------------------------------------------------------------------------------

print' :: ZigZag ix -> ix -> IO ()
print' ZZig = print
print' ZZag = print

printLeftSpineOf :: Zig -> IO ()
printLeftSpineOf =  go . enter
  where
    go :: Loc ZigZag Zig -> IO ()
    go loc = print' `on` loc >> maybe (return ()) go (down loc)

-------------------------------------------------------------------------------
-- test
-------------------------------------------------------------------------------

test :: IO ()
test =  printLeftSpineOf z
  where
    z = Zig (Zag (Zig Zap))