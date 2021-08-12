-- import Control.Monad.IO
import System.Random
import System.Environment

main = do (arg:_) <- getArgs
          let n = read arg
          g <- getStdGen
          genParens g n

genParens :: StdGen -> Int -> IO ()
genParens _ 0 = return ()
genParens g n = do
   let (b,g') = random g
   if b then putChar ')'
        else putChar '('
   genParens g' (n-1)
