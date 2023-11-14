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

Inductive ctx : Set :=
| Hole
| Node0 (l : ctx) (x : Z) (r : tree)
| Node2 (l : tree) (x : Z) (r : ctx).

Fixpoint comp (z1 : ctx) (z2 : ctx) : ctx :=
  match z1 with
  | Node0 zl x r => Node0 (comp zl z2) x r
  | Node2 l x zr => Node2 l x (comp zr z2)
  | Hole => z2
  end.

Fixpoint plug (z : ctx) (t : tree) : tree :=
  match z with
  | Node0 zl x r => Node (plug zl t) x r
  | Node2 l x zr => Node l x (plug zr t)
  | Hole => t
  end.

(* Context laws *)

Lemma comp_plug (z1 : ctx) (z2 : ctx) (t : tree)
  : plug (comp z1 z2) t = plug z1 (plug z2 t).
Proof.
  induction z1.
  - simpl; done.
  - simpl; rewrite IHz1; done.
  - simpl; rewrite IHz1; done.
Qed.