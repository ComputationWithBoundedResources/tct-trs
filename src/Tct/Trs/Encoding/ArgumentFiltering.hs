{- | 
This module provides a SAT encoding of argument filterings.
By convention, n-ary function symbols admit argument positions '[1..n]'.
-}
module Tct.Trs.Encoding.ArgumentFiltering 
where


data AFAtom f
  = Collapsing f
  | InFilter f Int
  deriving (Eq, Ord, Show)

{-isCollapsing :: (Eq l, Ord l) => Symbol -> PropFormula l-}
{-isCollapsing = propAtom . Collapsing -}

{-isInFilter :: (Eq l, Ord l) => Symbol -> Int -> PropFormula l-}
{-isInFilter sym pos = propAtom $ InFilter sym pos-}


{-initial :: Signature -> ArgumentFiltering-}
{-initial sig = Set.fold (alter mk) (empty sig) $ symbols sig-}
  {-where mk _ = Just $ Filtering $ IntSet.empty-}

{-insert :: AFAtom -> ArgumentFiltering -> ArgumentFiltering-}
{-insert (Collapsing sym) af = alter f sym af-}
  {-where f Nothing              = Just $ Projection 0-}
        {-f (Just (Filtering s)) = case IntSet.elems s of-}
                                   {-[p] -> Just $ Projection p-}
                                   {-_   -> error "ArgumentFiltering.insert: collapsing on multiple positions"-}
        {-f _                    =  error "ArgumentFiltering.insert: The impossible Happened"-}
{-insert (InFilter sym pos) af = alter f sym af-}
  {-where f Nothing               = Just $ Filtering $ IntSet.singleton pos-}
        {-f (Just (Projection 0)) = Just $ Projection pos-}
        {-f (Just (Filtering s))  = Just $ Filtering $ IntSet.insert pos s-}
        {-f _                    =  error "ArgumentFiltering.insert: reassining collapsing position"-}

{-instance Decoder ArgumentFiltering AFAtom where add = insert-}

{-validSafeArgumentFiltering :: (Eq l, Ord l) => [Symbol] -> Signature -> PropFormula l-}
{-validSafeArgumentFiltering syms sig = forall syms assertValid-}
  {-where assertValid sym | arity sig sym == 0 = not $ isCollapsing sym-}
                        {-| isCompound sig sym = not (isCollapsing sym) && (forall (argumentPositions sig sym) $ \ pos -> isInFilter sym pos)-}
                        {-| otherwise          = isCollapsing sym --> exactlyOne [isInFilter sym pos | pos <- argumentPositions sig sym]-}
