module Sandpit.Shapes

import Data.List1
import Data.List.Quantifiers

namespace Logic
  public export
  data Logic = Two | Four

  public export
  LOGIC : Type
  LOGIC = Maybe Logic

  public export
  TWO : LOGIC
  TWO = Just Two

  public export
  FOUR : LOGIC
  FOUR = Just Four

  public export
  NEUTRAL : LOGIC
  NEUTRAL = Nothing

  public export
  max : Logic -> Logic -> Logic
  max Two  _ = Two
  max _  Two = Two
  max Four Four = Four

  public export
  merge : LOGIC -> LOGIC -> LOGIC
  merge x y = max <$> x <*> y

namespace Packable
  public export
  data Packable = Packed | PackedUn

  public export
  PACKABLE : Type
  PACKABLE = Maybe Packable

  public export
  PACKED : PACKABLE
  PACKED = Just Packed

  public export
  PACKEDUN : PACKABLE
  PACKEDUN = Just PackedUn

  public export
  NEUTRAL : PACKABLE
  NEUTRAL = Nothing

  public export
  max : Packable -> Packable -> Packable
  max Packed Packed = Packed
  max _ PackedUn = PackedUn
  max PackedUn _ = PackedUn

  public export
  merge : PACKABLE -> PACKABLE -> PACKABLE
  merge x y = max <$> x <*> y

namespace Signable

  public export
  data Signable = Signed | SignedUn

  public export
  SIGNABLE : Type
  SIGNABLE = Maybe Signable


  public export
  NEUTRAL : SIGNABLE
  NEUTRAL = Nothing

  public export
  SIGNED : SIGNABLE
  SIGNED = Just Signed

  public export
  SIGNEDUN : SIGNABLE
  SIGNEDUN = Just SignedUn

  public export
  max : Signable -> Signable -> Signable
  max Signed Signed = Signed
  max SignedUn _        = SignedUn
  max _        SignedUn = SignedUn

  public export
  merge : SIGNABLE -> SIGNABLE -> SIGNABLE
  merge x y = max <$> x <*> y

namespace Size
  public export
  record Num where
    constructor N
    value : Maybe Nat

  public export
  num : Nat -> Num
  num n = N (Just n)

  public export
  binOp : (Nat -> Nat -> Nat) -> Num -> Num -> Num
  binOp op x y = N $ op <$> (value x) <*> (value y)

  public export
  plus : Num -> Num -> Num
  plus = binOp plus

  public export
  mult : Num -> Num -> Num
  mult = binOp mult

  public export
  max : Num -> Num -> Num
  max = binOp max

namespace Property

  public export
  record Properties where
    constructor P
    logic : LOGIC
    packed : PACKABLE
    signed : SIGNABLE
    size   : Num

  public export
  Merge : Properties -> Properties -> Properties
  Merge (P a b c d) (P x y z w)
    = P (merge a x)
        (merge b y)
        (merge c z)
        (plus d w)

  public export
  Merge' : Properties -> Properties -> Properties
  Merge' (P a b c d) (P x y z w)
    = P (merge a x)
        (merge b y)
        (merge c z)
        (max d w)

  public export
  Merge'' : Properties -> Properties -> Properties
  Merge'' (P a b c d) (P x y z w)
    = P (merge a x)
        (merge b y)
        (merge c z)
        (mult d w)

  public export
  Sum : List1 Properties -> Properties
  Sum (head ::: tail)
    = foldl Merge head tail

  public export
  Max : List1 Properties -> Properties
  Max (head ::: tail)
    = foldl Merge' head tail

  public export
  Vect : Nat -> Properties -> Properties
  Vect k = { size $= mult (num k)}

namespace Types
  mutual
    public export
    data Ty : Properties -> Type where
      TyInt    : Ty (P TWO     PACKED  SIGNED   (num 32))
      TyBit    : Ty (P TWO     PACKED  SIGNEDUN (num 1))
      TyLogic  : Ty (P FOUR    PACKED  SIGNEDUN (num 1))
      TyByte   : Ty (P TWO     PACKED  SIGNED   (num 8))
      TyTime   : Ty (P FOUR    PACKED  SIGNEDUN (num 64))
      TyString : Ty (P NEUTRAL NEUTRAL SIGNEDUN (num 64))

      TyVect : (n : Nat)
            -> (type : Ty p)
                    -> Ty (Vect n p)

      TyStruct : (ss : List1 String) -> TyKVs1 ss ps -> Ty (Sum ps)
      TyUnion  : (ss : List1 String) -> TyKVs1 ss ps -> Ty (Max ps)

    public export
    data TyKV : String -> Properties -> Type where
      KV : (s : String) -> (Ty p) -> TyKV s p

    public export
    data TyKVs : List String -> List Properties -> Type where
      Nil  : TyKVs Nil Nil
      (::) : TyKV s p
          -> TyKVs ss ps
          -> TyKVs (s::ss) (p::ps)

    public export
    data TyKVs1 : List1 String -> List1 Properties -> Type where
      KVS : TyKVs  (s ::ss) (p ::ps)
         -> TyKVs1 (s:::ss) (p:::ps)


-- [ EOF ]
