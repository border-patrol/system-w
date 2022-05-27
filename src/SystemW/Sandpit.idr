||| Playing with ideas.
|||
||| Module    : Sandpit.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see ../../LICENSE
|||
module SystemW.Sandpit

import Data.String
import Decidable.Equality
import Data.Fin
import Data.List.Elem

import Data.SortedSet

%default total

||| A Simple API for MultiGraphs.
namespace MultiGraph

  public export
  record Graph where
    constructor G
    vertices : SortedSet Nat
    edges    : List (Pair Nat Nat)

  export
  pretty : Graph -> String
  pretty (G vs es)
    = trim $ unwords $
      [ "digraph g {"
      , unwords $ map (\(s,t) => "\{show s} -> \{show t};") es

      , "}"
      ]

  namespace SystemW
    public export
    empty : Graph
    empty = G empty Nil

  public export
  addVertex : Nat -> Graph -> Graph
  addVertex n (G vs es)
    = G (insert n vs) es

  public export
  addEdge : (Nat, Nat) -> Graph -> Graph
  addEdge (a,b)
    = { edges $= (::) (a,b) }


  public export
  addEdges : List (Nat, Nat) -> Graph -> Graph
  addEdges es g = foldl addEdge' g es
    where
      addEdge' : Graph -> (Nat, Nat) -> Graph
      addEdge' g (a,b) = addEdge (a,b) (addVertex b (addVertex a g))

  public export
  fromEdges : List (Nat, Nat) -> Graph
  fromEdges es = addEdges es empty

  public export
  merge : Graph -> Graph -> Graph
  merge a g
    = foldl (flip addEdge) (foldl (flip addVertex) g (vertices a)) (edges a)

  public export
  replace : (inThis   : Graph)
         -> (src,trgt : Nat)
         -> (base     : Nat)
                     -> Graph
  replace (G vs es) s t a
      = G ((fromList . newVertices . SortedSet.toList) vs)
          (map fix es)
    where
      swap : Nat -> Nat
      swap i = if i == s
               then t
               else plus i a

      fix : (Nat, Nat) -> (Nat, Nat)
      fix (a,b) = (swap a, swap b)

      newVertices : List Nat -> List Nat
      newVertices = map swap

  public export
  max : Graph -> Nat
  max (G vs _)
    = case (reverse . SortedSet.toList) vs of
        Nil => Z
        (x::_) => x

||| DataTypes
namespace DataType
  public export
  data DataType = LOGIC | VECT Nat DataType

||| Term Types
namespace Ty
  namespace Property

    public export
    data Direction = IN | OUT

  public export
  data Ty : Type where

    Port : (shape : DataType)
        -> (dir   : Direction)
                 -> Ty
    Chan : (shape : DataType)
                 -> Ty

    Mod  : Ty -> Ty -> Ty
    Gate : Ty
    Unit : Ty

||| Typing Contexts
namespace Context

  public export
  Interp : Ty -> Type
  Interp (Port d y)
    = Nat
  Interp (Chan s)
    = (Nat, Nat)

  Interp (Mod a u)
    = Nat -> Interp a -> Interp u

  Interp Gate
    = Graph
  Interp Unit
    = Graph

  public export
  record Item where
    constructor I
    type   : Ty
    denote : Interp type


||| Accumulator Definition
namespace Accum
  public export
  record Accum where
    constructor A
    counter : Nat
    graph   : Graph

  public export
  Init : Accum
  Init
    = A Z SystemW.empty

  public export
  inc : Accum -> Accum
  inc = { counter $= S }

  public export
  setCounter : Nat -> Accum -> Accum
  setCounter i (A _ g)
    = A i g

  public export
  addVertex : Accum -> Accum
  addVertex a = { counter $= S, graph $= addVertex (S a.counter) } a

  public export
  addEdge : Accum -> Accum
  addEdge a = let s = S a.counter
              in let t = S s in { counter $= (S . S), graph $= addEdge (s,t) } a

  public export
  merge : Graph -> Accum -> Accum
  merge g = { graph $= merge g }

  public export
  advance : Graph -> Accum -> Accum
  advance g = {counter $= plus (max g), graph $= merge g}

||| Terms!
namespace Term

  public export
  data Term : (inA    : Accum)
           -> (ctxt   : List Item)
           -> (type   : Ty)
           -> (denote : Interp type)
           -> (outA   : Accum)
                     -> Type
    where
      Stop : Term i
                    ctxt Unit (graph i)
                  i

      Var : Elem (I ty de) ctxt
         -> Term i
                   ctxt ty de
                 i

      Mod : (dtype : DataType)
         -> (dir   : Direction)
         -> (scope : Term (A (S c) SystemW.empty)
                          (I (Port dtype dir) (S c) :: Nil)
                          Unit
                          g
                          outA)
                  -> Term (A c SystemW.empty)
                               ctxt (Mod (Port dtype dir) Unit)
                                    (\a, v => replace g (S c) v a)
                          outA

      Decl : (mod : Term (A (counter i) SystemW.empty)
                            ctxt (Mod (Port dtype dir) Unit) g
                         k)
           -> (scope : Term (setCounter (counter k) i)
                               (I (Mod (Port dtype dir) Unit) g :: ctxt) Unit g'
                            j)
                    -> Term i
                               ctxt Unit g'
                            j

      Plug : (mod : Term (A (S c) SystemW.empty)
                            ctxt  (Mod (Port dtype dir) Unit)
                                 f
                         o)
          -> (epo : Term (A (S c) ig)
                            ctxt (Port dtype dir)
                                 v
                         j)
          -> (scope : Term (advance (f (S c) v) j)
                              ctxt Unit g
                           k)
                 -> Term (A c ig)
                            ctxt Unit g
                         k

      Wire : (dtype : DataType)
          -> (scope : Term (addEdge i)
                                       (I (Chan dtype) (S i.counter, S (S i.counter)) :: ctxt)
                                       Unit
                                       g
                           o)
                   -> Term i
                               ctxt Unit g
                           o



      Gate : (outport : Term i
                                ctxt (Port LOGIC OUT) vo
                             j)
          -> (inportA : Term j
                                ctxt (Port LOGIC IN)  va
                             k)
          -> (inportB : Term k
                                ctxt (Port LOGIC IN)  vb
                             l)
                     -> Term i
                               ctxt Gate (fromEdges [ (va, S l.counter)
                                                    ,                     (S l.counter, vo)
                                                    , (vb, S l.counter)])

                             (inc l)

      GDecl : (gate  : Term i
                                 ctxt Gate g
                            j)
           -> (scope : Term (merge g j)
                              (I Gate g :: ctxt) Unit g'
                            k)
                    -> Term i
                              ctxt Unit g'
                            k

      Index : (port : Term i
                             ctxt (Port (VECT size ty) dir) v
                           o)
           -> (idx  : Fin size)
                   -> Term i
                             ctxt (Port            ty  dir) v
                           o


      ProjR : (chan : Term i ctxt (Chan ty)     (s,t) o)
                   -> Term i ctxt (Port ty IN)     t  o

      ProjW : (chan : Term i ctxt (Chan ty)     (s,t) o)
                   -> Term i ctxt (Port ty OUT)  s    o

      Catch : (chan : Term i ctxt (Port ty IN) v o)
                   -> Term i ctxt Gate
                                  (fromEdges [(v, S i.counter)])
                           (inc o)
      Drive : (chan : Term i ctxt (Port ty OUT) v o)
                   -> Term i ctxt Gate
                                  (fromEdges [(S i.counter, v)])
                           (inc o)

  public export
  record SystemW where
    constructor Top
    state : Accum
    graph : Graph
    term  : Term Init Nil Unit graph state

||| Examples
namespace Examples

  export
  example : SystemW
  example
    = Top _ _
      $ Decl (Mod LOGIC OUT
             $ GDecl (Drive (Var Here))
             $ Stop)
      $ Wire LOGIC
      $ Wire LOGIC
      $ Plug (Var (There (There Here)))
             (ProjW (Var Here))
      $ Plug (Var (There (There Here)))
             (ProjW (Var (There Here)))
      $ Stop


  export
  example0 : SystemW
  example0
    = Top _ _
      $ Decl (Mod LOGIC IN
             $ Wire LOGIC
             $ GDecl (Gate (ProjW (Var Here))
                           (Var (There Here))
                           (Var (There Here)))
             $ GDecl (Catch (Var (There (There Here))))
             $ Stop)
      $ Decl (Mod LOGIC OUT
             $ GDecl (Drive (Var Here))
             $ Stop)
      $ Wire LOGIC
      $ Plug (Var (There (There Here)))
             (ProjR (Var Here))
      $ Plug (Var (There Here))
             (ProjW (Var Here))
      $ Stop


  export
  example1 : SystemW
  example1
    = Top _ _
      $ Wire LOGIC
      $ GDecl (Drive (ProjW (Var Here)))
      $ Wire LOGIC
      $ GDecl (Gate  (ProjW (Var Here))
                     (ProjR (Var (There $ There Here)))
                     (ProjR (Var (There $ There Here)))
              )

      $ GDecl (Catch (ProjR (Var (There Here))))

       Stop


  export
  example2 : SystemW
  example2
    = Top _ _
      $ Decl (Mod LOGIC IN
             $ Wire LOGIC
             $ GDecl (Gate (ProjW (Var Here))
                           (Var (There Here))
                           (Var (There Here)))
             $ GDecl (Catch (ProjR (Var (There Here))))
             $ Stop)
      $ Wire LOGIC
      $ Plug (Var (There Here))
             (ProjR (Var Here))
      $ Plug (Var (There Here))
             (ProjR (Var Here))
      $ Stop


-- [ EOF ]
