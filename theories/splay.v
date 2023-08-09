From fip_iris Require Import lang tree.

(* Recursive *)

Fixpoint smaller (i : Z) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l x r =>
    if bool_decide (i = x)%Z then
      l
    else if bool_decide (i < x)%Z then
      match l with
      | Leaf => Leaf
      | Node ll lx lr =>
        if bool_decide (i = lx)%Z then
          ll
        else if bool_decide (i < lx)%Z then
          smaller i ll
        else
          Node ll lx (smaller i lr)
      end
    else
      match r with
      | Leaf => Node l x Leaf
      | Node rl rx rr =>
        if bool_decide (i = rx)%Z then
          Node l x rl
        else if bool_decide (i < rx)%Z then
          Node l x (smaller i rl)
        else
          Node (Node l x rl) rx (smaller i rr)
      end
  end.

Fixpoint bigger (i : Z) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l x r =>
    if bool_decide (i = x)%Z then
      r
    else if bool_decide (i < x)%Z then
      match l with
      | Leaf => Node Leaf x r
      | Node ll lx lr =>
        if bool_decide (i = lx)%Z then
          Node lr x r
        else if bool_decide (i < lx)%Z then
          Node (bigger i ll) lx (Node lr x r)
        else
          Node (bigger i lr) x r
      end
    else
      match r with
      | Leaf => Leaf
      | Node rl rx rr =>
        if bool_decide (i = rx)%Z then
          rr
        else if bool_decide (i < rx)%Z then
          Node (bigger i rl) rx rr
        else
          bigger i rr
      end
  end.

Definition rec_insert_go (i : Z) (t : tree) : root_tree :=
  Root (smaller i t) i (bigger i t).

Definition rec_insert (i : Z) (t : tree) : tree :=
  to_tree (rec_insert_go i t).

Local Hint Unfold smaller bigger rec_insert rec_insert_go : trees.

(* Bottom-up *)

Fixpoint splay (z : zipper) (t : root_tree) : root_tree :=
    match t with
    | Root tl tx tr =>
      match z with
      | Done => t
      | NodeL Done lx lr => Root tl tx (Node tr lx lr)
      | NodeL (NodeL up x r) lx lr => splay up (Root tl tx (Node tr lx (Node lr x r)))
      | NodeL (NodeR l x up) lx lr => splay up (Root (Node l x tl) tx (Node tr lx lr))
      | NodeR rl rx Done => Root (Node rl rx tl) tx tr
      | NodeR rl rx (NodeR l x up) => splay up (Root (Node (Node l x rl) rx tl) tx tr)
      | NodeR rl rx (NodeL up x r) => splay up (Root (Node rl rx tl) tx (Node tr x r))
      end
    end.

Fixpoint bu_insert_go (i : Z) (z : zipper) (t : tree) : root_tree :=
  match t with
  | Node l x r =>
    if bool_decide (i = x)%Z then
      splay z (Root l i r)
    else if bool_decide (i < x)%Z then
      match l with
      | Node ll lx lr =>
        if bool_decide (i = lx)%Z then
          splay z (Root ll i (Node lr x r))
        else if bool_decide (i < lx)%Z then
          bu_insert_go i (NodeL (NodeL z x r) lx lr) ll
        else
          bu_insert_go i (NodeR ll lx (NodeL z x r)) lr
      | Leaf => splay z (Root Leaf i (Node Leaf x r))
      end
    else
      match r with
      | Node rl rx rr =>
        if bool_decide (i = rx)%Z then
          splay z (Root (Node l x rl) i rr)
        else if bool_decide (i < rx)%Z then
          bu_insert_go i (NodeL (NodeR l x z) rx rr) rl
        else
          bu_insert_go i (NodeR rl rx (NodeR l x z)) rr
      | Leaf => splay z (Root (Node l x Leaf) i Leaf)
      end
  | Leaf => splay z (Root Leaf i Leaf)
  end.

Definition bu_insert (i : Z) (t : tree) : tree :=
  to_tree (bu_insert_go i Done t).

Local Hint Unfold bu_insert bu_insert_go : trees.

(* Published bottom-up *)

Fixpoint bu_insert_pub_go (i : Z) (z : zipper) (t : tree) : root_tree :=
    match t with
    | Node l x r =>
      if bool_decide (i = x)%Z then
        splay z (Root l x r)
      else if bool_decide (i < x)%Z then
        bu_insert_pub_go i (NodeL z x r) l
      else 
        bu_insert_pub_go i (NodeR l x z) r
    | Leaf => splay z (Root Leaf i Leaf)
    end.

Definition bu_insert_pub (i : Z) (t : tree) : tree :=
  to_tree (bu_insert_pub_go i Done t).

(* Top-down *)

Fixpoint td_insert_go (i : Z) (lctx : ctx) (rctx : ctx) (t : tree) :=
  match t with
  | Node l x r =>
    if bool_decide (i = x)%Z then
      (lctx, Root l i r, rctx)
    else if bool_decide (i < x)%Z then
      match l with
      | Node ll lx lr =>
        if bool_decide (i = lx)%Z then
          (lctx, Root ll i lr, comp rctx (Node0' x r))
        else if bool_decide (i < lx)%Z then
          td_insert_go i lctx (comp rctx (Node0' lx (Node lr x r))) ll
        else
          td_insert_go i (comp lctx (Node2' ll lx)) (comp rctx (Node0' x r)) lr
      | Leaf => (lctx, Root Leaf i (Node Leaf x r), rctx)
      end
    else
      match r with
      | Node rl rx rr =>
        if bool_decide (i = rx)%Z then
          (comp lctx (Node2' l x), Root rl i rr, rctx)
        else if bool_decide (i > rx)%Z then
          td_insert_go i (comp lctx (Node2' (Node l x rl) rx)) rctx rr
        else
          td_insert_go i (comp lctx (Node2' l x)) (comp rctx (Node0' rx rr)) rl
      | Leaf => (lctx, Root (Node l x Leaf) i Leaf, rctx)
      end
  | Leaf => (lctx, Root Leaf i Leaf, rctx)
  end.

Definition td_insert (i : Z) (t : tree) : tree :=
  match td_insert_go i Hole Hole t with
  | (lctx, Root l i r, rctx) => Node (plug lctx l) i (plug rctx r)
  end.

Local Hint Unfold td_insert td_insert_go : trees.

(* Proof of equivalence *)

Lemma rec_is_bu_go (i : Z) : forall t z,
  splay z (rec_insert_go i t) = bu_insert_go i z t.
Proof.
  fix IH 1. intros [|l x r] z. done.
  autounfold with trees.
  repeat case_bool_decide.
  - done.
  - destruct l as [|ll lx lr]. { done. } repeat case_bool_decide.
    + done.
    + now rewrite <- IH.
    + now rewrite <- IH.
  - destruct r as [|rl rx rr]. { done. } repeat case_bool_decide.
    + done.
    + now rewrite <- IH.
    + now rewrite <- IH.
Qed.

Lemma rec_is_bu (i : Z) (t : tree) : rec_insert i t = bu_insert i t.
Proof. autounfold with trees. now rewrite <- rec_is_bu_go. Qed.

Lemma rec_is_td_go (i : Z) : forall t lctx rctx,
   Node (plug lctx (smaller i t)) i (plug rctx (bigger i t)) = 
     match td_insert_go i lctx rctx t with
     | (lctx, Root l i r, rctx) => Node (plug lctx l) i (plug rctx r)
     end.
Proof.
  fix IH 1. intros [|l x r] lctx rctx. done.
  autounfold with trees.
  repeat case_bool_decide.
  - done.
  - destruct l as [|ll lx lr]. { done. } repeat case_bool_decide.
    + now rewrite comp_plug.
    + rewrite <- IH. now rewrite comp_plug.
    + rewrite <- IH. now do 2 rewrite comp_plug.
  - destruct r as [|rl rx rr]. { done. }
    repeat case_bool_decide; try (exfalso; lia).
    + now rewrite comp_plug.
    + rewrite <- IH. now do 2 rewrite comp_plug.
    + rewrite <- IH. now rewrite comp_plug.
Qed.

Lemma rec_is_td (i : Z) (t : tree) : rec_insert i t = td_insert i t.
Proof. autounfold with trees. now rewrite <- rec_is_td_go. Qed.

Lemma td_is_bu (i : Z) (t : tree) : bu_insert i t = td_insert i t.
Proof. now rewrite <- rec_is_bu, rec_is_td. Qed.

(* But the published bottom-up is _not_ equivalent: *)

Definition example_tree : tree
  := Node Leaf 1 (Node Leaf 2 (Node Leaf 3 Leaf)).

Lemma td_example : td_insert 4 example_tree
  = Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) 4 Leaf.
Proof. reflexivity. Qed.

Lemma bu_example : bu_insert_pub 4 example_tree
  = Node (Node Leaf 1 (Node (Node Leaf 2 Leaf) 3 Leaf)) 4 Leaf.
Proof. reflexivity. Qed.

(* Properties of splay trees *)

Inductive all (P : Z -> Type) : tree -> Type :=
| all_leaf : all P Leaf
| all_node : forall {l : tree} {x : Z} {r : tree},
             all P l -> P x -> all P r -> all P (Node l x r).

Local Hint Constructors all : trees.

Lemma all_impl {P Q : Z → Set} {t : tree} (H : all P t) (f : forall x : Z, P x → Q x) : all Q t.
Proof.
  induction t; [ now trivial with trees | ].
  inversion H; now auto with trees.
Qed.

Local Hint Resolve all_impl : trees.
