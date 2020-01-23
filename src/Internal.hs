{-# LANGUAGE DataKinds #-}

module Internal where

import TH

import qualified Data.Map.Strict as Map

unionWith :: (a -> b -> c) -> (a -> c) -> (b -> c) -> [(Int, a)] -> [(Int, b)] -> [(Int, c)]
unionWith _ _ f [] ys = fmap (fmap f) ys
unionWith _ f _ xs [] = fmap (fmap f) xs
unionWith f g h xs@((ix,vx):xs') ys@((iy,vy):ys')
    | ix == iy = (ix, f vx vy) : unionWith f g h xs' ys'
    | ix <  iy = (ix, g vx) : unionWith f g h xs' ys
    | ix >  iy = (iy, h vy) : unionWith f g h xs ys'

addLists :: (Num a, Eq a) => [(Int, a)] -> [(Int, a)] -> [(Int, a)]
addLists [] ys = ys
addLists xs [] = xs
addLists xs@((ix,vx):xs') ys@((iy,vy):ys')
    | ix == iy = let vz = vx + vy
                     zs = addLists xs' ys' in
                 if vz == 0
                 then zs
                 else (ix, vz) : zs
    | ix < iy = (ix, vx) : addLists xs' ys
    | ix > iy = (iy, vy) : addLists xs ys'

permSign [] = 1
permSign (_:[]) = 1
permSign (x:xs)
    | even (length defects) = permSign xs
    | odd (length defects)  = (-1) * permSign xs
  where
    defects = filter (<x) xs

trianMapSym2 :: Integral a => a -> Map.Map (Vec (S (S Z)) Int) Int
trianMapSym2 n = Map.fromList $ zip indices2 indices1
  where
    maxInd   = fromIntegral n - 1
    indices1 = [0..]
    indices2 = [a `VCons` (b `VCons` VNil) | a <- [0..maxInd], b <- [a..maxInd] ]

trianMapArea :: Map.Map (Vec (S (S (S (S Z)))) Int) Int
trianMapArea = Map.fromList $ zip indices4 indices1
  where
    indices1 = [0..]
    indices4 = [a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil))) |
                  a <- [0..2],
                  b <- [a+1..3],
                  c <- [a..2],
                  d <- [c+1..3],
                  not (a == c && b > d) ]

facMapSym2 :: (Integral a, Num b) => a -> Map.Map (Vec (S (S Z)) Int) b
facMapSym2 n = Map.fromList $ [(a `VCons` (b `VCons` VNil), fac a b) |
                                  a <- [0..maxInd], b <- [a..maxInd] ]
  where
    maxInd = fromIntegral n - 1
    fac a b
      | a == b    = 1
      | otherwise = 2

facMapArea :: Num b => Map.Map (Vec (S (S (S (S Z)))) Int) b
facMapArea = Map.fromList $ [(a `VCons` (b `VCons` (c `VCons` (d `VCons` VNil))), fac a b c d) |
                                a <- [0..2],
                                b <- [a+1..3],
                                c <- [a..2],
                                d <- [c+1..3],
                                not (a == c && b > d)]
  where
    fac a b c d
      | a == c && b == d = 4
      | otherwise        = 8
