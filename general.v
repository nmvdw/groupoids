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
    cbn.
    rewrite concat_1p.
    rewrite (eta_path_universe_uncurried 1).
    rewrite path_sigma_hprop_1.
    reflexivity.
  Defined.
  
  Definition path_hset_id {A : hSet} : path_hset (equiv_idmap A) = idpath.
  Proof.
    cbn.
    rewrite concat_1p.
    rewrite (eta_path_universe_uncurried 1).
    rewrite path_sigma_hprop_1.
    reflexivity.
  Defined.

  Definition path_sigma_hprop_inv
        {A : Type}
        (B : A -> hProp)
        {u v : A}
        (p : u = v)
        (x : B u) (y : B v)
    : @path_sigma_hprop A B _ (v;y) (u;x) p^ = (path_sigma_hprop (u;x) (v;y) p)^.
  Proof.
    induction p ; simpl.
    assert (q : x = y).
    { apply path_ishprop. }
    rewrite q.
    rewrite path_sigma_hprop_1.
    reflexivity.
  Defined.
  
  Definition path_hset_inv
             {A B : hSet}
             (f : Equiv A B)
    : path_hset f^-1 = (path_hset f)^.
  Proof.
    cbn.
    rewrite !concat_1p, !concat_p1.
    rewrite path_universe_V_uncurried.
    rewrite (path_sigma_hprop_inv
               (fun Z => BuildhProp (IsHSet Z))
               (path_universe_uncurried f)
               (istrunc_trunctype_type A)
               (istrunc_trunctype_type B)).
    rewrite ap_V.
    reflexivity.
  Defined.

  Definition path_universe_uncurried_transitive
             {A B C : Type}
             (f : Equiv A B) (g : Equiv B C)
    : path_universe_uncurried (transitive_equiv A B C f g)
      =
      path_universe_uncurried f @ path_universe_uncurried g.
  Proof.
    apply path_universe_compose.
  Defined.

  Definition path_sigma_hprop_concat
             {A : Type}
             (B : A -> hProp)
             {u v w : A}
             (p : u = v) (q : v = w)
             (x : B u) (y : B v) (z : B w)
    : @path_sigma_hprop A B _ (u;x) (w;z) (p @ q)
      =
      path_sigma_hprop (u;x) (v;y) p @ path_sigma_hprop (v;y) (w;z) q.
  Proof.
    induction p, q.
    assert(r₁ : y = x).
    { apply path_ishprop. }
    assert(r₂ : z = x).
    { apply path_ishprop. }
    rewrite r₁, r₂.
    rewrite !path_sigma_hprop_1.
    reflexivity.
  Defined.
  
  Definition path_hset_comp
             {A B C : hSet}
             (f : Equiv A B) (g : Equiv B C)
    : path_hset (transitive_equiv _ _ _ f g) = path_hset f @ path_hset g.
  Proof.
    cbn.
    rewrite !concat_1p, !concat_p1.
    rewrite path_universe_uncurried_transitive.
    rewrite (path_sigma_hprop_concat
               (fun Z => BuildhProp (IsHSet Z))
               (path_universe_uncurried f)
               (path_universe_uncurried g)
               (istrunc_trunctype_type A)
               (istrunc_trunctype_type B)
               (istrunc_trunctype_type C)).
    rewrite ap_pp.
    reflexivity.
  Defined.

  Definition path_hset_eq
             {A B : hSet}
             (f : Equiv A B) (g : Equiv A B)
             (fg_eq : equiv_fun f == equiv_fun g)
    : path_hset f = path_hset g.
  Proof.
    refine (ap path_hset _).
    rewrite <- (eisretr (issig_equiv A B) f).
    rewrite <- (eisretr (issig_equiv A B) g).
    apply (ap (issig_equiv A B)).
    cbn.
    simple refine (path_sigma' _ _ _) ; cbn.
    - exact (path_forall _ _ fg_eq).
    - apply path_ishprop.
  Defined.
End path_hset_prop.
