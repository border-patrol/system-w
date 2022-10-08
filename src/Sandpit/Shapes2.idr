module Sandpit.Shapes2

import Data.String
import Data.List1
import Data.DPair
import Data.List.Quantifiers
import Data.List1.Quantifiers

data Property : (0 i : Maybe Bool) -> Type where
  X : Property (Just False)
  Y : Property (Just True)
  Z : Property Nothing

Show (Property p) where
  show X = "X"
  show Y = "Y"
  show Z = "Z"

namespace Bool

    public export
    data Meet : (x,y,z : Maybe Bool) -> Type where
      LowerFT : Meet (Just False) (Just True)  (Just True)
      LowerTF : Meet (Just True)  (Just False) (Just True)
      Id    : Meet (Just a)     (Just a)    (Just a)
      NA    : Meet Nothing      a           Nothing
      AN    : Meet a            Nothing     Nothing

    public export
    0
    meet : (x,y : Maybe Bool) -> DPair (Maybe Bool) (Meet x y)
    meet Nothing y = (Nothing ** NA)
    meet (Just x) Nothing = (Nothing ** AN)
    meet (Just False) (Just False) = (Just False ** Id)
    meet (Just False) (Just True) = (Just True ** LowerFT)
    meet (Just True) (Just False) = (Just True ** LowerTF)
    meet (Just True) (Just True) = (Just True ** Id)

    public export
    sym : Meet x y z -> Meet y x z
    sym LowerFT = LowerTF
    sym LowerTF = LowerFT
    sym Id = Id
    sym NA = AN
    sym AN = NA

    public export
    MeetF : (x,y : Maybe Bool) -> Maybe Bool
    MeetF x y
      = max <$> x <*> y

    public export
    meet' : (x,y : Maybe Bool) -> (Meet x y (MeetF x y))
    meet' Nothing y = NA
    meet' (Just x) Nothing = AN
    meet' (Just False) (Just False) = Id
    meet' (Just False) (Just True) = LowerFT
    meet' (Just True) (Just False) = LowerTF
    meet' (Just True) (Just True) = Id

public export
meet : (  x   : Property a)
   -> (  y   : Property b)
            -> Property (MeetF a b)
meet X X = X
meet Y X = Y
meet Z X = Z
meet X Y = Y
meet Y Y = Y
meet Z Y = Z
meet X Z = Z
meet Y Z = Z
meet Z Z = Z

namespace Logic
  public export
  data Logic = L (Property l)

  public export
  TWO : Logic
  TWO = L X

  public export
  FOUR : Logic
  FOUR = L Y

  public export
  NEUTRAL : Logic
  NEUTRAL = L Z

  public export
  meet : Logic -> Logic -> Logic
  meet (L a) (L b)= L (meet a b)

namespace Packable
  public export
  data Packable = P (Property l)

  public export
  PACKED : Packable
  PACKED = P X

  public export
  PACKEDUN : Packable
  PACKEDUN = P Y

  public export
  NEUTRAL : Packable
  NEUTRAL = P Z

  public export
  meet : Packable -> Packable -> Packable
  meet (P a) (P b) = P (meet a b)

namespace Signable
  public export
  data Signable = S (Property l)

  public export
  SIGNED : Signable
  SIGNED = S X

  public export
  SIGNEDUN : Signable
  SIGNEDUN = S Y

  public export
  NEUTRAL : Signable
  NEUTRAL = S Z

  public export
  meet : Signable -> Signable -> Signable
  meet (S a) (S b) = S (meet a b)

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
  join : Num -> Num -> Num
  join = binOp max



namespace Property

  public export
  record Properties where
    constructor P
    logic : Logic
    packed : Packable
    signed : Signable
    size   : Num

  public export
  Sum : Properties -> Properties -> Properties
  Sum (P a b c d) (P x y z w)
    = P (meet a x)
        (meet b y)
        (meet c z)
        (plus d w)

  public export
  Union : Properties -> Properties -> Properties
  Union (P a b c d) (P x y z w)
    = P (meet a x)
        (meet b y)
        (meet c z)
        (join d w)

  namespace List1
    public export
    Sum : List1 Properties -> Properties
    Sum (head ::: tail)
      = foldl Sum head tail

    public export
    Union : List1 Properties -> Properties
    Union (head ::: tail)
      = foldl Union head tail

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

      TyStruct : All Ty ps -> Ty (Sum ps)
      TyUnion  : All Ty ps -> Ty (Union ps)

public export
foo : Ty (Sum (P TWO PACKED SIGNED (num 32) ::: [P TWO PACKED SIGNEDUN (num 1)]))
foo = TyStruct (All.(:::) TyInt (All.(::) TyBit Nil))

foo' : Ty (P TWO PACKED SIGNEDUN (num 33))
foo' = foo

showAll : (f : forall x . p x -> String) -> List.Quantifiers.All.All p xs -> String
showAll f [] = ""
showAll f (x :: Nil) = "\{f x}"
showAll f (x :: y) = "\{f x}, \{showAll f y}"


showAll1 : (f : forall x . p x -> String) -> List1.Quantifiers.All.All p xs -> String
showAll1 f (x ::: y) = "[\{f x}, \{showAll f y}]"

showTy : Ty p -> String
showTy TyInt = "I"
showTy TyBit = "B"
showTy TyLogic = "L"
showTy TyByte = "B"
showTy TyTime = "T"
showTy TyString = "S"
showTy (TyVect n type) = "[\{showTy type}; \{show n}]"
showTy (TyStruct x) = "{\{showAll1 showTy x}}"
showTy (TyUnion x) = "<\{showAll1 showTy x}>"

Show Packable where
  show (P a) = "P \{show a}"

Show Num where
  show (N a) = "N \{show a}"

Show Logic where
  show (L a) = "L \{show a}"

Show Signable where
  show (S a) = "S \{show a}"

Show Properties where
  show (P logic packed signed size)
    = "(P \{show logic} \{show packed} \{show signed} \{show size})"
namespace Main
  export
  main : IO ()
  main = do putStrLn (showTy foo)
            putStrLn (showTy foo')
            putStrLn (show X)
            printLn (show ((P TWO PACKED SIGNEDUN (num 33))))
-- [ EOF ]
