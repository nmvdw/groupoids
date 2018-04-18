Require Import HoTT.

Definition curry
           {X Y Z : Type}
           (f : X * Y -> Z)
  : X -> Y -> Z
  := fun x y => f(x, y).

Definition uncurry_ap
           {X Y Z : Type}
           (f : X -> Y -> Z)
           {x₁ x₂ : X} {y₁ y₂ : Y}
           (p : x₁ = x₂) (q : y₁ = y₂)
  : ap (uncurry f) (path_prod' p q)
    =
    ap (fun z => f z y₁) p @ ap (f x₂) q
  := match p, q with
     | idpath, idpath => idpath
     end.

Definition curry_ap
           {X Y Z : Type}
           (f : X * Y -> Z)
           {x₁ x₂ : X * Y}
           (p : x₁ = x₂)
  : ap f p
    =
    (ap (fun z => curry f z (snd x₁)) (ap fst p))
      @ (ap (fun z => curry f (fst x₂) z) (ap snd p))
  := match p with
     | idpath => idpath
     end.

Definition ap_pair_l
           {X Y : Type}
           {x₁ x₂ : X} (y : Y)
           (p : x₁ = x₂)
  : ap (fun x => (x, y)) p = path_prod' p idpath
  := match p with
     | idpath => idpath
     end.

Definition ap_pair_r
           {X Y : Type}
           (x : X) {y₁ y₂ : Y}
           (q : y₁ = y₂)
  : ap (pair x) q = path_prod' idpath q
  := match q with
     | idpath => idpath
     end.

Section path_hset_prop.
  Context `{Univalence}.

  Definition path_hset' {A B : hSet} (f : A -> B) {feq : IsEquiv f} : (A = B)
  := path_hset (BuildEquiv _ _ f feq).

  Lemma path_hset_1 {A : hSet} : path_hset' (fun x : A => x) = 1%path.
  Proof.
    cbn. hott_simpl.
    rewrite (eta_path_universe_uncurried 1).
    rewrite path_sigma_hprop_1.
    hott_simpl.
  Defined.

End path_hset_prop.
