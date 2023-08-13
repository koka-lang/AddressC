(* Copyright (c) 2023 Microsoft Research, Anton Lorenzen *)

From fip_iris Require Import lang.

Inductive tree : Set :=
| Leaf
| Node (l : tree) (x : Z) (r : tree).

Inductive root_tree : Set :=
| Root (l : tree) (x : Z) (r : tree).

Definition get_root : root_tree -> Z :=
  fun r => match r with
           | Root _ x _ => x
           end.

Definition to_tree: root_tree -> tree :=
  fun r => match r with
           | Root l x r => Node l x r
           end.

(* Bottom-up *)

Inductive zipper : Set :=
| Done
| NodeL (l : zipper) (x : Z) (r : tree)
| NodeR (l : tree) (x : Z) (r : zipper).

(* Top-down *)

Inductive ctx0 : Set :=
| Node0 (z : ctx0) (x : Z) (r : tree)
| Node2 (l : tree) (x : Z) (z : ctx0)
| Node0' (* Hole *) (x : Z) (r : tree)
| Node2' (l : tree) (x : Z) (* Hole *).

Inductive ctx : Set :=
| Ctx0 (z : ctx0)
| Hole.

Fixpoint comp0 (z1 z2 : ctx0) : ctx0 :=
  match z1 with
  | Node0 zl x r => Node0 (comp0 zl z2) x r
  | Node2 l x zr => Node2 l x (comp0 zr z2)
  | Node0' x r => Node0 z2 x r
  | Node2' l x => Node2 l x z2 
  end.

Definition comp' (z1 : ctx) (z2 : ctx0) : ctx0 :=
  match z1 with
  | Ctx0 z1 => comp0 z1 z2
  | Hole => z2
  end.

Definition comp (z1 : ctx) (z2 : ctx0) : ctx :=
  Ctx0 (comp' z1 z2).

Fixpoint plug0 (z : ctx0) (t : tree) : tree :=
  match z with
  | Node0 zl x r => Node (plug0 zl t) x r
  | Node2 l x zr => Node l x (plug0 zr t)
  | Node0' x r => Node t x r
  | Node2' l x => Node l x t
  end.

Definition plug (z : ctx) (t : tree) : tree :=
  match z with
  | Ctx0 z => plug0 z t
  | Hole => t
  end.

(* Context laws *)

Lemma comp_plug (z : ctx) (z' : ctx0) (t : tree)
  : plug (comp z z') t = plug z (plug (Ctx0 z') t).
Proof.
    destruct z.
    - induction z; simpl; try (unfold plug, comp in IHz; rewrite IHz); done.
    - unfold plug, comp; done.
Qed.