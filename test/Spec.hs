import Generator
import Test.QuickCheck

main :: IO ()
main = do
    quickCheck (withMaxSuccess 100 propWellTyped)
    quickCheck (withMaxSuccess 100 propSemPreservation)