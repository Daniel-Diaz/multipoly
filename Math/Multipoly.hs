
-- | Polynomials with finite number of variables.
--   Each variable is indexed with a value of type 'Int' (an 'Index').
--
--
module Math.Multipoly (
    Index
  , Positive (..)
  , Natural (..)
  , Exponent
  , MultiPoly
  , zeroPoly
  , monomial
  , scalePoly
  , evalPoly
  , derivePoly
  , degree
  , homogenize
  , filterPoly
  , sumCoeffs
  ) where

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Monoid
import Data.List (intersperse)

-- | Index of a polynomial variable.
type Index = Int

-- | A positive natural number.
data Positive = One | Succ Positive deriving Eq

positiveToInt :: Positive -> Int
positiveToInt = go 1
  where
    go x (Succ p) = go (x+1) p
    go x One = x

positiveFromInt :: Int -> Maybe Positive
positiveFromInt n = if n <= 0 then Nothing else Just $ go One n
  where
    go p 1 = p
    go p n = go (Succ p) (n-1)

instance Show Positive where
  show = show . positiveToInt

instance Ord Positive where
  Succ p <= Succ q = p <= q
  p <= _ = p == One

infixl 6 +., -.

-- | Sum of positive numbers.
(+.) :: Positive -> Positive -> Positive
Succ p +. q = p +. Succ q
One +. p = Succ p

-- | Monoid of positive numbers with multiplication.
instance Monoid Positive where
  mempty = One
  mappend (Succ p) q = mappend p q +. q
  mappend One p = p

-- | Positive numbers substraction.
(-.) :: Positive -> Positive -> Maybe Positive
Succ p -. Succ q = p -. q
Succ p -. One = Just p
_ -. _ = Nothing

positiveExp :: Monoid a => a -> Positive -> a
positiveExp x = go x
  where
    go a (Succ p) = go (x <> a) p
    go a One = a

-- | Exponent of a polynomial variable.
type Exponent = Positive

-- | A Variable Map indicates the exponent of each index
--   in a monomial.
type VariableMap = Map Index Exponent

-- | Polynomial with any number of variables.
newtype MultiPoly a = MultiPoly (Map VariableMap a) deriving Eq

-- | Monomial builder. You can create polynomials by adding monomials.
monomial :: [(Index,Exponent)] -- ^ List of indices with exponents.
         -> a                  -- ^ Coefficient
         -> MultiPoly a
monomial = (MultiPoly .) . M.singleton . M.fromList

-- | Zero polynomial.
zeroPoly :: MultiPoly a
zeroPoly = MultiPoly M.empty

polyOperate :: Num a => (a -> a -> a) -> (MultiPoly a -> MultiPoly a -> MultiPoly a)
polyOperate f (MultiPoly p) (MultiPoly q) = MultiPoly $ M.fromList $ fmap g ks
  where
    g k = (k , M.findWithDefault 0 k p `f` M.findWithDefault 0 k q)
    ks = M.keys $ M.union p q

-- | Multiplication of monomials.
multMonomial :: Num a => (VariableMap,a) -> (VariableMap,a) -> (VariableMap,a)
multMonomial (v,k) (w,l) = (M.unionWith (+.) v w,k*l)

showVariableMap :: VariableMap -> String
showVariableMap vm = mconcat $ fmap (
  \(i,e) -> "x(" ++ show i ++ ")" ++
      if e > One then "^" ++ show e
                 else ""
     ) $ M.toList vm

instance Show a => Show (MultiPoly a) where
  show (MultiPoly p) =
    if M.null p
       then "0"
       else unwords $ intersperse "+" $
              fmap (\(vm,k) -> show k ++
                       if M.null vm
                          then ""
                          else "*" ++ showVariableMap vm) $ M.toList p

instance Functor MultiPoly where
  fmap f (MultiPoly p) = MultiPoly $ fmap f p

instance Num a => Num (MultiPoly a) where
  fromInteger n = if n == 0 then zeroPoly else monomial [] $ fromInteger n
  (+) = polyOperate (+)
  (-) = polyOperate (-)
  MultiPoly p * MultiPoly q = MultiPoly $ M.fromListWith (+) $
    [ multMonomial a b
      | let as = M.toList p
      , let bs = M.toList q
      , a <- as , b <- bs
      ]
  abs = fmap abs
  signum = fmap signum
  negate = fmap negate

-- | Multiply all coefficients of a polynomial by a constant.
scalePoly :: Num a => a -> MultiPoly a -> MultiPoly a
scalePoly = fmap . (*)

-- | Evaluate one of the variables of a polinomial.
evalPoly :: Num a
         => Index -- ^ Index of the variable.
         -> a     -- ^ Value to assign.
         -> MultiPoly a -> MultiPoly a
evalPoly v a (MultiPoly p) = MultiPoly $ M.foldrWithKey f M.empty p
  where
    f vm k =
      case M.lookup v vm of
        Nothing -> M.insert vm k
        Just e -> M.insert (M.delete v vm) $ k * getProduct (positiveExp (Product a) e)

-- | Derivative of a polynomial with respect to one variable.
derivePoly :: Num a
           => Index -- ^ Derivation variable
           -> MultiPoly a
           -> MultiPoly a
derivePoly v (MultiPoly p) = MultiPoly $ M.foldrWithKey f M.empty p
  where
    f vm k =
      case M.lookup v vm of
        Nothing -> id
        Just e -> M.insert (M.update (-.One) v vm) $ getSum $ positiveExp (Sum k) e

-- | A 'Natural' number is either 'Zero' or a 'Positive' number.
data Natural = Zero | Pos Positive deriving Eq

sumNat :: [Natural] -> Natural
sumNat = foldr s Zero
  where
    s Zero n = n
    s n Zero = n
    s (Pos p) (Pos q) = Pos $ p +. q

naturalToInt :: Natural -> Int
naturalToInt Zero = 0
naturalToInt (Pos p) = positiveToInt p

instance Show Natural where
  show = show . naturalToInt

instance Ord Natural where
  Zero <= _ = True
  _ <= Zero = False
  Pos p <= Pos q = p <= q

-- | Calculate the degree of a polynomial. It returns 'Nothing' for the polynomial
--   zero ('zeroPoly'), for this polynomial has no degree defined.
degree :: MultiPoly a -> Maybe Natural
degree (MultiPoly p)
  | M.null p = Nothing
  | otherwise = Just $ maximum $ fmap (sumNat . fmap Pos . M.elems) $ M.keys p

-- | Polynomial homogenization. It returns both the new polynomial and the
--   'Index' of the new variable.
--
--   If the following condition is satisfied:
--
-- > 1 * x = x * 1 = x , for all x :: a
--
--   Then the following equation holds for any @p :: MultiPoly a@:
--
-- > let (q,i) = homogenize p
-- > in  p = evalPoly i 1 q
--
--   This means that you can return to the original polynomial by evaluating
--   the homogenized polymial at @1@ with respect to the added variable.
--
homogenize :: MultiPoly a -> (MultiPoly a,Int)
homogenize mp@(MultiPoly p) = (h,k)
  where
    is = S.unions $ fmap M.keysSet $ M.keys p
    go i = if S.member i is then go (i+1) else i
    k = go 0
    d = degree mp
    h = case d of
          Nothing -> mp
          Just Zero -> mp
          Just (Pos n) ->
            -- 'f' takes a Variable Map and adds the new variable
            -- with exponent enough to raise the degree of the monomial to n.
            let f vm = case degree $ MultiPoly $ M.fromList [(vm,error "homogenize: bug in 'degree' function.")] of
                         Nothing -> error "homogenize: This cannot happen! BUG!"
                         -- Monomial of degree zero.
                         Just Zero -> M.fromList [(k,n)]
                         -- Monomial of positive degree.
                         Just (Pos m) ->
                           case n -. m of
                             -- The degree of the monomial is already n: return the original.
                             Nothing -> vm
                             -- The degree of the monomial is less than n: add the difference.
                             Just e -> M.insert k e vm
            in  MultiPoly $ M.mapKeys f p

-- | Select the monomials such that its coefficient satisfies a given condition.
--
--   Useful to clean out zeroes with @filterPoly (/= 0)@. We don't do this automatically
--   since a 'Num' instance does not imply an 'Eq' instance, and there can be interesting
--   polynomials whose coefficients are not an instance of 'Eq'.
filterPoly :: (a -> Bool) -> MultiPoly a -> MultiPoly a
filterPoly f (MultiPoly p) = MultiPoly $ M.filter f p

-- | Return the sum of all the coefficients in a polynomial. If the polynomial has 'degree' zero,
--   you might want to use this function to quickly retrieve its one and only coefficient.
--   Use this idea in combination with 'evalPoly' if you are able to predict the number of
--   variables your polynomial use. For example, let @p = 2*x1^2*x2 + x1@.
--   To evaluate this polynomial in @(x1,x2) = (3,1)@, it suffices to do:
--
-- > sumCoeffs . evalPoly 2 1 . evalPoly 1 3 $ p = 21
--
--   Since we know the variables in @p@ are @x1@ and @x2@, after evaluating both of them we know
--   the result is of degree 0, and then we use 'sumCoeffs' to retrieve its constant value.
sumCoeffs :: Num a => MultiPoly a -> a
sumCoeffs (MultiPoly p) = sum $ M.elems p
