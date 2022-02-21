import Generator
import Test.QuickCheck

main :: IO ()
main = do
    putStrLn "Testing terms are well typed"
    quickCheck (withMaxSuccess 200 propWellTyped)
    putStrLn "Testing semantic preservation in unroll"
    quickCheck (withMaxSuccess 200 propSemPreservation)
    putStrLn "Trivial tests to coverage Show instances"
    quickCheck (withMaxSuccess 30 propTrivialShow)
    quickCheck (withMaxSuccess 5 propTrivialShowName)