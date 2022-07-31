{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import qualified Data.Dependent.Map as DMap
import Data.Dependent.Sum ((==>))
import Data.Functor.Identity (Identity (..))
import Data.GADT.Compare (GCompare (..), GEq (..), GOrdering (..))
import Data.Kind (Constraint, Type)
import Data.Singletons (Demote, KindOf, Sing, SingKind, fromSing, sing)
import Data.Singletons.TH (genSingletons)
import Data.Some (Some (..))
import qualified Data.Type.Bool as Bool
import Data.Type.Equality ((:~:) (..), type (==))
import qualified GHC.TypeLits as Lits
import Prelude.Singletons (PEq)

type Canonical :: k -> k
type family Canonical t

type Canon :: k -> Constraint
type Canon t = Canonical t ~ t

type instance Canonical 'Nothing = 'Nothing

type instance Canonical ('Just v) = 'Just v

type family Fun (x :: c) :: d -> c where
  Fun (f v) = f

type family Arg (x :: c) :: d where
  Arg (f v) = v

type family Args (k :: Type) (n :: Type) :: Type where
  Args (d -> c) n = Args c (d, n)
  Args c n = n

type CanonicalByHead :: Type -> hk -> vk -> vk
type family CanonicalByHead (k :: Type) (h :: hk) (v :: vk) :: vk where
  CanonicalByHead (d, c) h (v :: vk) =
    CanonicalByHead c h (Fun v :: d -> vk) (Canonical (Arg v :: d))
  CanonicalByHead () h v = h

data ExistsV (f :: k) where
  MkExistsV :: CanonicalByHead (Args k ()) (f :: k) t ~ t => t -> ExistsV f

type family TypeFor (k :: f v) where
  TypeFor (k :: f v) = v

newtype Var (k :: f v) = Var v

type instance Canonical v = 'Var (Arg v)

type Use :: Var (k :: f v) -> v
type family Use vv where
  Use ('Var v) = v

type (^.) :: t -> f i -> i
type family (^.) v k where
  (^.) (f (x :: Var k)) k = Use x
  (^.) (f x) k = (^.) f k

data Condition where
  Same :: k -> k -> Condition
  And :: Condition -> Condition -> Condition
  Or :: Condition -> Condition -> Condition
  Not :: Condition -> Condition

type (=~=) = 'Same

type (&~&) = 'And

type (|~|) = 'Or

class CanEval c where
  type Eval c :: Bool

instance CanEval ('Same l r) where
  type Eval ('Same l r) = l == r

instance CanEval ('And l r) where
  type Eval ('And l r) = Eval l Bool.&& Eval r

instance CanEval ('Or l r) where
  type Eval ('Or l r) = Eval l Bool.|| Eval r

instance CanEval ('Not x) where
  type Eval ('Not x) = Bool.Not (Eval x)

type CheckCondition :: Condition -> Bool -> Constraint
type family CheckCondition c o where
  CheckCondition c o =
    ( o ~ 'True,
      Bool.If
        (o == 'True)
        (() :: Constraint)
        ( Lits.TypeError
            ( 'Lits.Text "Field cannot be used due to false condition:"
                'Lits.:$$: 'Lits.ShowType c
                'Lits.:$$: 'Lits.Text ""
                'Lits.:$$: 'Lits.Text "To resolve, either:"
                'Lits.:$$: 'Lits.Text "- Switch from `Yep _` to `Nah` (or `YepS _` to `NahS`)"
                'Lits.:$$: 'Lits.Text "- Update other fields to make the condition true"
                'Lits.:$$: 'Lits.Text ""
            )
        )
    )

type RefuteCondition :: Condition -> Bool -> Constraint
type family RefuteCondition c o where
  RefuteCondition c o =
    ( o ~ 'False,
      Bool.If
        (o == 'False)
        (() :: Constraint)
        ( Lits.TypeError
            ( 'Lits.Text "Field must be used due to true condition:"
                'Lits.:$$: 'Lits.ShowType c
                'Lits.:$$: 'Lits.Text ""
                'Lits.:$$: 'Lits.Text "To resolve, either:"
                'Lits.:$$: 'Lits.Text "- Switch from `Nah` to `Yep _` (or `NahS` to `YepS _`)"
                'Lits.:$$: 'Lits.Text "- Update other fields to make the condition false"
                'Lits.:$$: 'Lits.Text ""
            )
        )
    )

data WhenS :: Condition -> Maybe k -> Type where
  YepS :: CheckCondition c (Eval c) => Sing v -> WhenS c ('Just v)
  NahS :: RefuteCondition c (Eval c) => WhenS c 'Nothing

type instance Canonical (WhenS c m) = WhenS c m

data When :: Condition -> Type -> Type where
  Yep :: CheckCondition c (Eval c) => t -> When c t
  Nah :: RefuteCondition c (Eval c) => When c t

type instance Canonical (When c t) = When c t

type CheckInvariant :: Condition -> Bool -> Constraint
type family CheckInvariant c o where
  CheckInvariant c o =
    ( o ~ 'True,
      Bool.If
        (o == 'True)
        (() :: Constraint)
        ( Lits.TypeError
            ( 'Lits.Text "Invariant violated:"
                'Lits.:$$: 'Lits.ShowType c
            )
        )
    )

data Invariant :: Condition -> Type where
  Invariant :: CheckInvariant c (Eval c) => Invariant c

---

data AB = A | B

data CD = C | D

instance PEq AB -- {{{

instance PEq CD

genSingletons [''AB, ''CD]

type instance Canonical (SAB v) = SAB v

type instance Canonical (SCD v) = SCD v -- }}}

-- the universe of names and types
data Field :: Type -> Type where
  F0 :: Field AB
  F1 :: Field CD
  F2 :: Field CD
  F3 :: Field CD

-- those fields that are depended on & their optionality
data Dep :: Type -> Type where
  F0_ :: Dep (TypeFor 'F0)
  F1_ :: Dep (TypeFor 'F1)
  F2_ :: Dep (Maybe (TypeFor 'F2))

-- $> :set -XDataKinds

-- promoted context of dependencies
data Ctx = Ctx
  { ctxF0 :: Var 'F0_,
    ctxF1 :: Var 'F1_,
    ctxF2 :: Var 'F2_
  }

type instance
  Canonical (ctx :: Ctx) =
    CanonicalByHead (Args (KindOf 'Ctx) ()) 'Ctx ctx

-- consistent domain data
data Domain :: Ctx -> Type where
  Domain ::
    { fieldF0 :: Sing f0,
      fieldF1 :: Sing f1,
      fieldF2 :: WhenS (f0 =~= 'A) f2,
      fieldF3 :: When (f2 =~= 'Just 'D) (TypeFor 'F3),
      fieldInvariant :: When ('Not (f2 =~= 'Nothing)) (Invariant (f1 =~= 'C))
    } ->
    Domain ('Ctx ('Var f0) ('Var f1) ('Var f2))

data SomeDomain where
  SomeDomain ::
    Canon ctx =>
    Domain ctx ->
    SomeDomain

-- example validated domain
egDomain :: SomeDomain
egDomain =
  SomeDomain
    Domain
      { fieldF0 = sing @('A),
        fieldF1 = sing @('C),
        fieldF2 = YepS (sing @('D)),
        fieldF3 = Yep C,
        fieldInvariant = Yep Invariant
      }

domainF0 :: Domain ctx -> Sing (ctx ^. 'F0_)
domainF0 (Domain {fieldF0}) = fieldF0

someDomainF3 :: SomeDomain -> Maybe CD
someDomainF3 (SomeDomain d) =
  case fieldF3 d of
    Nah -> Nothing
    Yep o -> Just o

usage0 :: Canon ctx => Domain ctx -> String
usage0 d =
  case fieldF2 d of
    YepS _ -> case fieldF0 d of
      SA -> ""
    NahS -> ""

usage1 :: Canon ctx => Domain ctx -> String
usage1 d =
  case fieldF0 d of
    SA ->
      case fieldF2 d of
        -- NahS -> ""
        YepS b -> case b of
          SC -> ""
          SD -> ""
    SB ->
      case fieldF2 d of
        NahS -> ""

-- fromCompleteDom0 :: Canon ctx => Domain ctx -> String
-- fromCompleteDom0 d =
--   case ( fieldF0 d,
--          fieldF1 d,
--          fieldF2 d,
--          fieldF3 d,
--          fieldInvariant d
--        ) of
--     (SA, SC, YepS SD, Yep C, Yep Invariant) -> "A C D C I"
--     (SA, SC, YepS SD, Yep D, Yep Invariant) -> "A C D D I"
--     (SA, SC, YepS SC, Nah, Yep Invariant) -> "A C C _ I"
--     (SB, SC, NahS, Nah, Nah) -> "B C _ _ _"
--     (SB, SD, NahS, Nah, Nah) -> "B D _ _ _"

fromCompleteDom :: Domain ctx -> String
fromCompleteDom = \case
  Domain SA SC (YepS SD) (Yep C) (Yep Invariant) -> "A C D C I"
  Domain SA SC (YepS SD) (Yep D) (Yep Invariant) -> "A C D D I"
  Domain SA SC (YepS SC) Nah (Yep Invariant) -> "A C C _ I"
  Domain SB SC NahS Nah Nah -> "B C _ _ _"
  Domain SB SD NahS Nah Nah -> "B D _ _ _"

{-# COMPLETE Demoted #-}

pattern Demoted :: forall k (a :: k). SingKind k => Demote k -> Sing a
pattern Demoted v <- (fromSing -> v)

{-# COMPLETE YepD, NahS #-}

pattern YepD ::
  forall k c (o :: Maybe k).
  (SingKind k) =>
  forall v.
  (CheckCondition c (Eval c), o ~ 'Just v) =>
  Demote k ->
  WhenS c o
pattern YepD v <- YepS (Demoted v)

fromCompleteDomEg0 :: Canon ctx => Domain ctx -> String
fromCompleteDomEg0 = \case
  Domain {fieldF2 = YepD C, fieldInvariant = Yep Invariant} -> ""
  Domain {fieldF2 = YepD D, fieldInvariant = Yep Invariant} -> ""
  Domain {fieldInvariant = Nah} -> "_"

data Atom :: Ctx -> Type -> Type where
  AtomF0 :: Atom ctx (Sing (ctx ^. 'F0_))
  AtomF1 :: Atom ctx (Sing (ctx ^. 'F1_))
  AtomF2 :: Atom ctx (WhenS (ctx ^. 'F0_ =~= 'A) (ctx ^. 'F2_))
  AtomF3 :: Atom ctx (When (ctx ^. 'F2_ =~= 'Just 'D) (TypeFor 'F3))
  AtomInvariant :: Atom ctx (When ('Not (ctx ^. 'F2_ =~= 'Nothing)) (Invariant (ctx ^. 'F1_ =~= 'C)))

instance GEq (Atom ctx) where
  geq AtomF0 AtomF0 = Just Refl
  geq AtomF1 AtomF1 = Just Refl
  geq AtomF2 AtomF2 = Just Refl
  geq AtomF3 AtomF3 = Just Refl
  geq AtomInvariant AtomInvariant = Just Refl
  geq _ _ = Nothing

instance GCompare (Atom ctx) where
  gcompare AtomF0 AtomF0 = GEQ
  gcompare AtomF0 _ = GLT
  gcompare _ AtomF0 = GGT
  gcompare AtomF1 AtomF1 = GEQ
  gcompare AtomF1 _ = GLT
  gcompare _ AtomF1 = GGT
  gcompare AtomF2 AtomF2 = GEQ
  gcompare AtomF2 _ = GLT
  gcompare _ AtomF2 = GGT
  gcompare AtomF3 AtomF3 = GEQ
  gcompare AtomF3 _ = GLT
  gcompare _ AtomF3 = GGT
  gcompare AtomInvariant AtomInvariant = GEQ

universe :: [Some (Atom ctx)]
universe =
  [ Some AtomF0,
    Some AtomF1,
    Some AtomF2,
    Some AtomF3,
    Some AtomInvariant
  ]

newtype Complete ctx = Complete {runComplete :: forall t. Atom ctx t -> t}

newtype Partial ctx = Partial {runPartial :: forall t. Atom ctx t -> Maybe t}

partialComplete :: Partial ctx -> Maybe (Complete ctx)
partialComplete (Partial p) = do
  f0 <- p AtomF0
  f1 <- p AtomF1
  f2 <- p AtomF2
  f3 <- p AtomF3
  invariant <- p AtomInvariant
  pure $ Complete \case
    AtomF0 -> f0
    AtomF1 -> f1
    AtomF2 -> f2
    AtomF3 -> f3
    AtomInvariant -> invariant

-- fromCompleteAtom0 :: Complete ctx -> String
-- fromCompleteAtom0 (Complete d) =
--   case (d AtomF0, d AtomF1, d AtomF2, d AtomF3, d AtomInvariant) of
--     (SA, SC, YepS SD, Yep C, Yep Invariant) -> "A C D C I"
--     (SA, SC, YepS SD, Yep D, Yep Invariant) -> "A C D D I"
--     (SA, SC, YepS SC, Nah, Yep Invariant) -> "A C C _ I"
--     (SB, SC, NahS, Nah, Nah) -> "B C _ _ _"
--     (SB, SD, NahS, Nah, Nah) -> "B D _ _ _"

completeDomain :: Canon ctx => Complete ctx -> Domain ctx
completeDomain (Complete d) =
  Domain
    { fieldF0 = d AtomF0,
      fieldF1 = d AtomF1,
      fieldF2 = d AtomF2,
      fieldF3 = d AtomF3,
      fieldInvariant = d AtomInvariant
    }

fromComplete :: Canon ctx => Complete ctx -> String
fromComplete = fromCompleteDom . completeDomain

fromPartial :: Canon ctx => Partial ctx -> Maybe String
fromPartial = fmap fromComplete . partialComplete

type MyBoog =
  'Ctx
    ('Var 'A)
    ('Var 'C)
    ('Var ('Just 'D))

completeBoog :: Complete MyBoog
completeBoog = Complete \case
  AtomF0 -> SA
  AtomF1 -> SC
  AtomF2 -> YepS SD
  AtomF3 -> Yep C
  AtomInvariant -> Yep Invariant

newtype Bag ctx = Bag {getBag :: DMap.DMap (Atom ctx) Identity}

egBag :: Bag MyBoog
egBag =
  Bag $
    DMap.fromList
      [ AtomF0 ==> SA,
        AtomF1 ==> SC,
        AtomF2 ==> YepS SD,
        AtomF3 ==> Yep C,
        AtomInvariant ==> Yep Invariant
      ]

bagDomain :: Canon ctx => Bag ctx -> Maybe (Domain ctx)
bagDomain (Bag b) = do
  Identity f0 <- DMap.lookup AtomF0 b
  Identity f1 <- DMap.lookup AtomF1 b
  Identity f2 <- DMap.lookup AtomF2 b
  Identity f3 <- DMap.lookup AtomF3 b
  Identity inv <- DMap.lookup AtomInvariant b
  pure $ Domain f0 f1 f2 f3 inv

fromBag :: Canon ctx => Bag ctx -> Maybe String
fromBag b = fromCompleteDom <$> bagDomain b

fromSomeBag :: ExistsV Bag -> Maybe String
fromSomeBag (MkExistsV b) = fromBag b

newtype Π f g = UnsafeCompleteBag (DMap.DMap f g)

compile ::
  GCompare (f c) =>
  [Some (f c)] ->
  DMap.DMap (f c) g ->
  Maybe (Π (f c) g)
compile uni b =
  if all (\(Some k) -> DMap.member k b) uni
    then Just (UnsafeCompleteBag b)
    else Nothing

at :: GCompare f => f i -> Π f g -> g i
at k (UnsafeCompleteBag b) = b DMap.! k

ix :: GCompare f => f i -> Π f Identity -> i
ix k b = runIdentity (at k b)

fromCompleteBag :: Π (Atom ctx) Identity -> String
fromCompleteBag b =
  fromCompleteDom $
    Domain
      (ix AtomF0 b)
      (ix AtomF1 b)
      (ix AtomF2 b)
      (ix AtomF3 b)
      (ix AtomInvariant b)

main :: IO ()
main = do
  putStrLn "∀ fromComplete completeBoog"
  putStrLn (fromComplete completeBoog)

  putStrLn "∀ fromBag egBag"
  mapM_ putStrLn (fromBag egBag)

  putStrLn "∀ fromSomeBag (MkExistsV egBag)"
  mapM_ putStrLn (fromSomeBag (MkExistsV egBag))

  putStrLn "∀ fromCompleteBag <$> compile universe (getBag egBag)"
  mapM_ putStrLn (fromCompleteBag <$> compile universe (getBag egBag))

  pure ()

-- $> main
