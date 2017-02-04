
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> {-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, FlexibleInstances #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE OverloadedStrings #-}
> {-# OPTIONS_GHC -fno-warn-missing-methods -fno-warn-orphans #-}

We specify a `Monoid` instance for a `newtype` of lists.

> import Data.Monoid ( Monoid(..) )

We use QuickCheck version 1 for testing because version 2 cannot be
used in batch mode.

> import Test.QuickCheck
> import Test.QuickCheck.Batch
> import Control.Monad ( ap, replicateM )
> import Data.Char ( chr, ord )
> import Data.List ( permutations )

We import the semiring properties in order to check them for the
defined instances. We also define our own `sum` function for
semirings.

> import Data.Semiring.Properties
> import Prelude hiding ( sum )

Finally, we need the `RegExp` datatype, the `symWeight` function from
the `Weight` class, and the different semirings used for matching.

> import Text.RegExp
> import Text.RegExp.Data
> import Text.RegExp.Matching.Leftmost.Type ( Leftmost(..) )
> import Text.RegExp.Matching.Longest.Type  ( Longest(..) )
> import Text.RegExp.Matching.LeftLong.Type ( LeftLong(..) )
> import Text.RegExp.Matching.Leftmost ( getLeftmost )
> import Text.RegExp.Matching.Longest  ( getLongest )
> import Text.RegExp.Matching.LeftLong ( getLeftLong )
> import qualified Text.RegExp.Matching.Leftmost as Leftmost
> import qualified Text.RegExp.Matching.Longest  as Longest
> import qualified Text.RegExp.Matching.LeftLong as LeftLong

The `main` function runs all tests defined in this program.

> main :: IO ()
> main = 
>  do runChecks "semiring laws (Bool)" (semiring'laws :: Checks Bool)
>     runChecks "semiring laws (Int)" (semiring'laws :: Checks (Numeric Int))
>     runChecks "semiring laws (Leftmost)" (semiring'laws :: Checks Leftmost)
>     runChecks "semiring laws (Longest)" (semiring'laws :: Checks Longest)
>     runChecks "semiring laws (LeftLong)" semiring'laws'LeftLong
>     runTests (pad "full match") options $
>       checks (full'match'spec acceptFull id :: Checks Bool) ++
>       checks (full'match'spec matchingCount getNumeric
>               :: Checks (Numeric Int))
>     runTests (pad "partial match") options $
>       checks (partial'match'spec acceptPartial id :: Checks Bool) ++
>       checks (indexed'match'spec Leftmost.matching getLeftmost) ++
>       checks (partial'match'spec Longest.matching getLongest) ++
>       checks (indexed'match'spec LeftLong.matching getLeftLong)
>     runTests (pad "parse printed regexp") options [run parse'printed]
>     runChecks "lazy infinite regexps" infinite'regexp'checks
>     runTests "permutation parsing" options [run perm'parser'check]
>  where
>   options = defOpt { no_of_tests = 1000, length_of_tests = 60 }
>   runChecks s = runTests (pad s) options . checks
>   pad s = replicate (25-length s) ' ' ++ s

The `Arbitrary` instance for numeric types wraps the underlying
instance. We also provide one for `Char` which is not predefined.

> instance (Num a, Arbitrary a) => Arbitrary (Numeric a) where
>   arbitrary = Numeric `fmap` arbitrary
>
> instance Arbitrary Char where
>   arbitrary = elements "abcde \\|*+?.[]{}"

We provide generic `Semiring` instances for the semirings used for
matching.

> instance Arbitrary Leftmost where
>   arbitrary = frequency [ (1, return zero)
>                         , (1, return one)
>                         , (3, (Leftmost . abs) `fmap` arbitrary) ]
>
> instance Arbitrary Longest where
>   arbitrary = frequency [ (1, return zero) 
>                         , (1, return one)
>                         , (3, (Longest . succ . abs) `fmap` arbitrary) ]
>
> instance Arbitrary LeftLong where
>   arbitrary = frequency [ (1, return zero)
>                         , (1, return one)
>                         , (3, do x <- abs `fmap` arbitrary
>                                  y <- abs `fmap` arbitrary
>                                  return $ LeftLong (min x y) (max x y)) ]

We define a list of `Checks` for the semiring laws.

> semiring'laws :: (Arbitrary s, Show s, Semiring s) => Checks s
> semiring'laws = mconcat [ prop2 plus'comm
>                         , prop1 left'zero
>                         , prop3 add'assoc
>                         , prop1 left'one
>                         , prop1 right'one
>                         , prop3 mul'assoc
>                         , prop3 left'distr
>                         , prop3 right'distr
>                         , prop1 left'ann
>                         , prop1 right'ann
>                         ]

`Checks` is a `newtype` for a list of batch tests with a phantom type
that can be used in definitions of the properties.

> newtype Checks a = Checks { checks :: [TestOptions -> IO TestResult] }
>  deriving ( Monoid )

We define the auxiliary functions to create semiring properties with
different arities.

> prop1 :: (Arbitrary s, Show s, Testable a) => (s -> a) -> Checks s
> prop1 prop = Checks [run prop]
>
> prop2 :: (Arbitrary s, Show s, Testable a) => (s -> s -> a) -> Checks s
> prop2 prop = Checks [run prop]
>
> prop3 :: (Arbitrary s, Show s, Testable a) => (s-> s -> s -> a) -> Checks s
> prop3 prop = Checks [run prop]

The `LeftLong` type satisfies the distributive laws only with a
precondition on all involved multiplications: multiplied matches must
be adjacent and the start position must be smaller than the end
position. This precondition is satisfied for all multiplications
during regular expression matching.

We define a variant of `semiring'laws` with this precondition on the
distributive laws.

> semiring'laws'LeftLong :: Checks LeftLong
> semiring'laws'LeftLong = mconcat
>   [ prop2 plus'comm
>   , prop1 left'zero
>   , prop3 add'assoc
>   , prop1 left'one
>   , prop1 right'one
>   , prop3 mul'assoc
>   , prop3 left'distr'LeftLong
>   , prop3 right'distr'LeftLong
>   , prop1 left'ann
>   , prop1 right'ann
>   ]

For testing the distributive laws, we adjust the randomly generated
`LeftLong` values such that the arguments of multiplications are
adjacent.

> left'distr'LeftLong :: LeftLong -> LeftLong -> LeftLong -> Bool
> left'distr'LeftLong a b c = left'distr a (shift a b) (shift a c)
>  where
>   shift (LeftLong _ x) (LeftLong y z) = LeftLong (x+1) (z+x+1-y)
>   shift _              x              = x
>
> right'distr'LeftLong :: LeftLong -> LeftLong -> LeftLong -> Bool
> right'distr'LeftLong a b c = right'distr (shift a c) (shift b c) c
>  where
>   shift (LeftLong x y) (LeftLong z _) = LeftLong (x+z-1-y) (z-1)
>   shift x              _              = x

Now we turn to the correctness of the `match` function. In order to
check it, we compare it with a executable specification which is
correct by definition:

> full'match'spec :: (Show a, Weight Char Char s)
>                 => (RegExp Char -> String -> a)
>                 -> (s -> a)
>                 -> Checks s
> full'match'spec = match'spec fullMatchSpec
>
> partial'match'spec :: (Show a, Weight Char Char s)
>                    => (RegExp Char -> String -> a)
>                    -> (s -> a)
>                    -> Checks s
> partial'match'spec = match'spec partialMatchSpec
>
> indexed'match'spec :: (Show a, Weight Char (Int,Char) s)
>                    => (RegExp Char -> String -> a)
>                    -> (s -> a)
>                    -> Checks s
> indexed'match'spec = match'spec (\r -> partialMatchSpec r . zip [(0::Int)..])
>
> match'spec :: (Show a, Semiring s)
>            => (RegExp Char -> String -> s)
>            -> (RegExp Char -> String -> a)
>            -> (s -> a)
>            -> Checks s
> match'spec spec convmatch conv =
>   Checks [run (check'match'spec spec convmatch conv)]
>

> check'match'spec :: (Show a, Semiring s)
>                  => (RegExp Char -> String -> s)
>                  -> (RegExp Char -> String -> a)
>                  -> (s -> a)
>                  -> RegExp Char -> String -> Bool
> check'match'spec spec convmatch conv r s =
>   show (convmatch r s') == show (conv (spec r s'))
>  where s' = take 5 s

To make this work, we need an `Arbitrary` instance for regular
expressions.

> instance Arbitrary (RegExp Char) where
>   arbitrary = sized regexp
>
> regexp :: Int -> Gen (RegExp Char)
> regexp 0 = frequency [ (1, return eps)
>                      , (4, char `fmap` simpleChar) ]
> regexp n = frequency [ (3, regexp 0)
>                      , (1, alt  `fmap` subexp `ap` subexp)
>                      , (2, seq_ `fmap` subexp `ap` subexp)
>                      , (1, rep  `fmap` regexp (n-1))
>                      , (2, fromString `fmap` parsedRegExp n) ]
>  where subexp = regexp (n `div` 2)
>
> simpleChar :: Gen Char
> simpleChar = elements "abcde"
>
> parsedRegExp :: Int -> Gen String
> parsedRegExp n = frequency [ (4, symClass)
>                            , (2, (++"?") `fmap` subexp)
>                            , (2, (++"+") `fmap` subexp)
>                            , (1, mkBrep1 =<< subexp)
>                            , (1, mkBrep2 =<< subexp) ]
>  where
>   subexp = (($"") . showParen True . shows)
>     `fmap` (resize (n-1) arbitrary :: Gen (RegExp Char))
>
>   mkBrep1 r = do x <- elements [0..3] :: Gen Int
>                  return $ r ++ "{" ++ show x ++ "}"
>
>   mkBrep2 r = do x <- elements [0..2] :: Gen Int
>                  y <- elements [0..2] :: Gen Int
>                  return $ r ++ "{" ++ show x ++ "," ++ show (x+y) ++ "}"
>
> symClass :: Gen String
> symClass = frequency [ (1, specialChar)
>                      , (2, do n <- choose (0,3)
>                               cs <- replicateM n charClass
>                               s <- (["","^"]!!) `fmap` choose (0,1)
>                               return $ "[" ++ s ++ concat cs ++ "]") ]
>  where
>   specialChar = elements (map (:[]) "." ++
>                           map (\c -> '\\':[c]) "abcdewWdDsS \\|*+?.[]{}^")
>   charClass   = oneof [ (:[]) `fmap` simpleChar
>                       , specialChar
>                       , do x <- simpleChar
>                            y <- simpleChar
>                            return $ x : '-' : [chr (ord x+ord y-ord 'a')] ]

The specification of the matching function is defined inductively on
the structure of a regular expression. It uses exhaustive search to
find all possibilities to match a regexp against a word.

> fullMatchSpec :: Weight a b s => RegExp a -> [b] -> s
> fullMatchSpec (RegExp r) = matchSpec (reg (weighted r))
>
> matchSpec :: Semiring s => Reg s c -> [c] -> s
> matchSpec Eps        u  =  if null u then one else zero
> matchSpec (Sym _ f)  u  =  case u of [c] -> f c; _ -> zero
> matchSpec (Alt p q)  u  =  matchSpec (reg p) u .+. matchSpec (reg q) u
> matchSpec (Seq p q)  u  =
>   sum [ matchSpec (reg p) u1 .*. matchSpec (reg q) u2 | (u1,u2) <- split u ]
> matchSpec (Rep p)    u  =
>   sum [ prod [ matchSpec (reg p) ui | ui <- ps] | ps <- parts u ]
>
> sum, prod :: Semiring s => [s] -> s
> sum   =  foldr (.+.) zero
> prod  =  foldr (.*.) one
>
> split :: [a] -> [([a],[a])]
> split []      =  [([],[])]
> split (c:cs)  =  ([],c:cs) : [ (c:s1,s2) | (s1,s2) <- split cs ]
>
> parts :: [a] ->  [[[a]]]
> parts []      =  [[]]
> parts [c]     =  [[[c]]]
> parts (c:cs)  =  concat [ [(c:p):ps,[c]:p:ps] | p:ps <- parts cs ]

We can perform a similar test for partial instead of full matches.

> partialMatchSpec :: Weight a b s => RegExp a -> [b] -> s
> partialMatchSpec (RegExp r) =
>   matchSpec (reg (arb `seqW` weighted r `seqW` arb))
>  where RegExp arb = rep anySym

As a check for the parser, we check whether the representation
generated by the `Show` instance of regular expressions can be parsed
back and yields the original expression.

> parse'printed :: RegExp Char -> Bool
> parse'printed r = fromString (show r) == r

We can also match infinite regular expressions lazily to recognize
context-free or even context-sensitive languages.

> infinite'regexp'checks :: Checks Bool
> infinite'regexp'checks = Checks [run context'free, run context'sensitive]

As an example for a context-free language, we recognize the language
 ${a^nb^n | n >= 0}$.

> context'free :: String -> Bool
> context'free s = isInAnBn s == (anbn =~ s)
>
> isInAnBn :: String -> Bool
> isInAnBn s = all (=='a') xs && all (=='b') ys && length xs == length ys
>  where (xs,ys) = break (=='b') s
>
> anbn :: RegExp Char
> anbn = eps `alt` seq_ "a" (anbn `seq_` "b")

As an example for a context-sensitive language we use the language
${a^nb^nc^n | n >= 0}$. To show that the alphabet cannot only contain
characters, we use numbers instead of characters.

> context'sensitive :: [Int] -> Bool
> context'sensitive s = isInAnBnCn s == acceptFull anbncn s
>
> isInAnBnCn :: [Int] -> Bool
> isInAnBnCn s = all (==1) xs && all (==2) ys && all (==3) zs
>             && length xs == length ys && length ys == length zs
>  where (xs,l)  = break (==2) s
>        (ys,zs) = break (==3) l
>
> anbncn :: RegExp Int
> anbncn = mkAnBnCn 0
>  where
>   mkAnBnCn n = brep (n,n) (sym 2) `seq_` brep (n,n) (sym 3)
>          `alt` seq_ (sym 1) (mkAnBnCn (n+1))

The library provides a combinator that matches a list of regular
expressions in sequence, each occurring once in any order.

> perm'parser'check :: String -> Bool
> perm'parser'check cs = all (acceptFull (perm (map char s))) (permutations s)
>  where s = take 5 cs

We restrict the test to at most 5! (that is five factorial)
permutations because otherwise there are too many. Note that it is
possible to match much longer permutations:

    ghci> accept (perm (map char ['a'..'z'])) $ reverse ['a'..'z']
    True
    (0.05 secs, 8706356 bytes)

But matching `perm (map char ['a'..'z'])` against *all* permutations
of ['a'..'z'] takes too long.

