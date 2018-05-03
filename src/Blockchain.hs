
-- (c) MP-I (1998/9-2006/7) and CP (2005/6-2018/9)

module Blockchain  where

import Cp
import Nat

-- (1) Datatype definition -----------------------------------------------------

inBlockchain = either Bc Bcs

outBlockchain (Bc b) = i1 b
outBlockchain (Bcs bs) = i2 bs


-- (2) Ana + cata + hylo -------------------------------------------------------

cataBlockchain g   = g . recBlockchain (cataBlockchain g) . outBlockchain   

recBlockchain  f   = id -|- id >< f                   -- this is F f for this data type

anaBlockchain  g   = inBlockchain . recBlockchain (anaBlockchain g) . g

hyloBlockchain h g = cataBlockchain h . anaBlockchain g

baseBlockchain f g = id -|- f >< g

-- (3) Map ---------------------------------------------------------------------
-- NB: already in the Haskell Prelude

-- (4) Examples ----------------------------------------------------------------

-- (4.1) number representation (base b) evaluator ------------------------------

eval b = cataBlockchain (either zero (add.(id><(b*))))

-- eval b [] = 0
-- eval b (x:xs) = x + b * (eval b xs)

-- (4.2) inversion -------------------------------------------------------------

invl = cataBlockchain (either nil snoc) where snoc(a,l) = l ++ [a]

-- alternatively: snoc = conc . swap . (singl >< id)
--                       where singl a = [a]
--                             conc = uncurry (++)

-- (4.3) Look-up function ------------------------------------------------------

look :: Eq a => a -> [(a,b)] -> Maybe b
look k = cataBlockchain (either nothing aux)
        where nothing = const Nothing
              aux((a,b),r)
                      | a == k    = Just b
                      | otherwise = r

-- (4.4) Insertion sort --------------------------------------------------------

iSort :: Ord a => [a] -> [a]
iSort =  cataBlockchain (either nil insert)
         where insert(x,[])              = [x]
               insert(x,a:l) | x < a     = [x,a]++l
                             | otherwise = a:(insert(x,l))

-- also iSort = hyloBlockchain (either (const []) insert) outBlockchain

-- (4.5) take (cf GHC.Blockchain.take) -----------------------------------------------

take' = curry (anaBlockchain aux)
         where aux(0,_) = i1()
               aux(_,[]) = i1()
        ---    aux(n+1,x:xs) = i2(x,(n,xs))
               aux(n,x:xs) = i2(x,(n-1,xs))

-- pointwise version:
-- take 0 _ = []
-- take _ [] = []
-- take (n+1) (x:xs) = x : take n xs

-- (4.6) Factorial--------------------------------------------------------------

fac = hyloBlockchain algMul nats

-- where

algMul = either (const 1) mul
--mul = uncurry (*)

nats = (id -|- (split succ id)) . outNat

-- (4.6.1) Factorial (alternative) ---------------------------------------------

fac' = hyloBlockchain (either (const 1) (mul . (succ >< id)))
                 ((id -|- (split id id)) . outNat)

{-- cf:

fac' = hyloBlockchain (either (const 1) g) nats'
       where g(n,m) = (n+1) * m
             nats' 0 = i1 ()
             nats' (n+1) = i2 (n,n)
--}

-- (4.7) Square function -------------------------------------------------------

{-- pointwise:
sq 0 = 0
sq (n+1) = 2*n+1 + sq n

cf. Newton's binomial: (n+1)^2 = n^2 + 2n + 1
--}

sq = hyloBlockchain summing odds

summing = either (const 0) add

odds = (id -|- (split impar id)) . outNat
       where impar n = 2*n+1

{-- odds pointwise:
odds 0 = i1 ()
odds (n+1) = i2 (2*n+1,n)
--}

-- (4.7.1) Square function reusing anaBlockchain of factorial ----------------------------

sq' = (cataBlockchain summing) . fmap (\n->2*n-1) . (anaBlockchain nats)

-- (4.8) Prefixes and suffixes -------------------------------------------------

prefixes :: Eq a => [a] -> [[a]]
prefixes = cataBlockchain (either (const [[]]) scan)
           where scan(a,l) = [[]] ++ (map (a:) l)

suffixes = anaBlockchain g
           where g = (id -|- (split cons p2)).outBlockchain

diff :: Eq a => [a] -> [a] -> [a]
diff x l = cataBlockchain (either nil (g l)) x
           where g l (a,x) = if (a `elem` l) then x else (a:x)

-- (4.9) Grouping --------------------------------------------------------------

--nest :: Int -> [a] -> [[a]]
nest n = anaBlockchain (g n) where
--         g n [] = i1()
--         g n l = i2(take n l,drop n l)
           g n = cond (==[]) (i1.(!)) (i2.(split (take n)(drop n)))

-- (4.10) Relationship with foldr, foldl ----------------------------------------

myfoldr :: (a -> b -> b) -> b -> [a] -> b
myfoldr f u = cataBlockchain (either (const u) (uncurry f))

myfoldl :: (a -> b -> a) -> a -> [b] -> a
myfoldl f u = cataBlockchain' (either (const u) (uncurry f . swap))
              where cataBlockchain' g   = g . recBlockchain (cataBlockchain' g) . outBlockchain'   
                    outBlockchain' [] = i1()
                    outBlockchain' x =i2(last x, blast x)
                    blast = tail . reverse

-- (4.11) Advanced --------------------------------------------------------------

-- (++) as a Blockchain catamorphism ------------------------------------------------

ccat :: [a] -> [a] -> [a]
ccat = cataBlockchain (either (const id) compose). map (:) where
       -- compose(f,g) = f.g
       compose =  curry(ap.(id><ap).assocr)

-- monadic map
mmap f = cataBlockchain $ either (return.nil)(fmap cons.dstr.(f><id))

-- distributive law
lam  :: Strong m => [m a] -> m [a]
lam = cataBlockchain ( either (return.nil)(fmap cons.dstr) )

-- monadic catas

mcataBlockchain :: Strong ff => (Either () (b, c) -> ff c) -> [b] -> ff c
mcataBlockchain g = g .! (dl . recBlockchain (mcataBlockchain g) . outBlockchain)   

dl :: Strong m => Either () (b, m a) -> m (Either () (b, a))
dl = either (return.i1)(fmap i2. lstr)

--lam' = mcataBlockchain (either (return.nil)(fmap cons.rstr))

-- streaming -------------------------------------------------------------------

stream f g c x = case f c of
   Just (b, c') -> b : stream f g c' x
   Nothing      ->  case x of
                      a:x' -> stream f g (g c a) x'
                      []   -> []

---- end of Blockchain.hs ------------------------------------------------------------
