
--TODO 種々のアルゴリズムの実装
--     Deltaのデータ構造がよろしくないので改良する
--     PDAにも手を出したい

module Main where

import Automaton

main :: IO ()
main = do
        let dfa2 = powersetConstruction nfa2
        print $ ""    `isAcceptedBy` nfa2 == ""    `isAcceptedBy` dfa2
        print $ "0"   `isAcceptedBy` nfa2 == "0"   `isAcceptedBy` dfa2
        print $ "01"  `isAcceptedBy` nfa2 == "01"  `isAcceptedBy` dfa2
        print $ "010" `isAcceptedBy` nfa2 == "010" `isAcceptedBy` dfa2

dfa1 :: Automaton String
dfa1 = Automaton { states      = ["q0","f"]
                 , alphabet    = ['1', '0']
                 , initState   = "q0"
                 , finalStates = ["f"]
                 , delta       = [ ("q0", Symbol '0', "f")
                                 , ("q0", Symbol '1', "q0")
                                 , ("f" , Symbol '0', "f")
                                 , ("f" , Symbol '1', "q0")
                                 ]
                   }

nfa2 :: Automaton String
nfa2 = Automaton { states      = ["q0","f"]
                 , alphabet    = ['1', '0']
                 , initState   = "q0"
                 , finalStates = ["f"]
                 , delta       = [ ("q0", Symbol '0', "f")
                                 , ("q0", Symbol '1', "q0")
                                 , ("f" , Symbol '0', "f")
                                 , ("f" , Null      , "q0")
                                 ]
                   }



printEither :: (Show a) => Either String a -> IO ()
printEither = either putStrLn print

