Require Import HoTT.
From GR Require Import
     general.
From GR.basics Require Export
     globe_over path_over square.
From HoTT.Categories Require Import
     Category GroupoidCategory Functor.
Require Import GR.groupoid.rezk_completion.rezk.

Local Open Scope category.

Section rezk_rec.
  Variable (C : PreCategory)
           (Y : Type)
           (rclY : C -> Y)
           (rcleqY : forall {x y : C},
               x <~=~> y -> rclY x = rclY y)
           (reY : forall (x : C), rcleqY (isomorphic_refl C x) = idpath)
           (rconcatY : forall {x y z : C} (g : y <~=~> z) (f : x <~=~> y),
               rcleqY (isomorphic_trans f g) = rcleqY f @ rcleqY g)
           (truncY : IsTrunc 1 Y).

  Definition rezk_rec : rezk C -> Y.
  Proof.
    simple refine (rezk_ind (fun _ => Y)
                             rclY
                             (fun x y f => const_path_over (rcleqY x y f))
                             (fun x => const_globe_over
                                         (path_to_globe (re C x))
                                         (rcleqY x x (isomorphic_refl C x))
                                         idpath
                                         (path_to_globe (reY x)))
                             _ _) ; cbn.
    intros x y z g f.
    simple refine (globe_over_whisker
                     (fun _ => Y)
                     _
                     idpath
                     (const_path_over_concat _ _)
                     (const_globe_over
                        (path_to_globe (rconcat C g f))
                        (rcleqY x z (isomorphic_trans f g))
                        (rcleqY x y f @ rcleqY y z g)
                        (path_to_globe (rconcatY x y z g f))
                     )
                  ).
  Defined.

  Definition rezk_rec_beta_rcleq {x y : C} (f : x <~=~> y)
    : ap rezk_rec (rcleq C f) = rcleqY x y f.
  Proof.
    apply (const_path_over_inj (rcleq C f)).
    refine ((apd_po_const _ _)^ @ _).
    apply rezk_ind_beta_rcleq.
  Qed.
End rezk_rec.

Arguments rezk_rec {C}.

(** If the we have a family of sets, then we can simplify the induction principle. *)
Section rezk_ind_set.
  Variable (C : PreCategory)
           (Y : rezk C -> Type)
           (rclY : forall (x : C), Y(rcl C x))
           (rcleqY : forall (x y : C) (f : x <~=~> y),
               path_over Y (rcleq C f) (rclY x) (rclY y))
           (truncY : forall (x : rezk C), IsHSet (Y x)).

  Definition rezk_ind_set : forall (x : rezk C), Y x.
  Proof.
    simple refine (rezk_ind Y rclY rcleqY _ _ _)
    ; intros ; apply path_globe_over_hset ; apply _.
  Defined.

  Definition rezk_ind_set_beta_rcl (x : C)
    : rezk_ind_set (rcl C x) = rclY x
    := idpath.

  Definition rezk_ind_set_beta_rcleq : forall {x y : C} (f : x <~=~> y),
      apd_po rezk_ind_set (rcleq C f)
      =
      rcleqY x y f.
  Proof.
    apply rezk_ind_beta_rcleq.
  Qed.
End rezk_ind_set.

Arguments rezk_ind_set {C} Y rclY rcleqY truncY.

(** If the we have a family of propositions, then we can simplify the induction principle. *)
Section rezk_ind_prop.
  Variable (C : PreCategory)
           (Y : rezk C -> Type)
           (rclY : forall (x : C), Y(rcl C x)).
  Context `{forall (x : rezk C), IsHProp (Y x)}.

  Definition rezk_ind_prop : forall (x : rezk C), Y x.
  Proof.
    simple refine (rezk_ind_set Y rclY _ _).
    intros ; apply path_over_path_hprop ; apply _.
  Qed.
End rezk_ind_prop.

Arguments rezk_ind_prop {C} Y rclY.

(** The double recursion principle.
    We use [gquot_rec], [gquot_ind_set] and [gquot_ind_prop] to define it.
 *)
Section rezk_double_rec.
  Variable (C₁ C₂ : PreCategory)
           (Y : Type).
  Context `{IsTrunc 1 Y}
          `{Funext}.

  Variable (f : C₁ -> C₂ -> Y)
           (fr : forall (x : C₁) (y₁ y₂ : C₂),
               y₁ <~=~> y₂ -> f x y₁ = f x y₂)
           (fre : forall (x : C₁) (y : C₂),
               fr x y y (isomorphic_refl C₂ y) = idpath)
           (frc : forall (x : C₁) (y₁ y₂ y₃ : C₂)
                         (g₂ : y₂ <~=~> y₃) (g₁ : y₁ <~=~> y₂),
               fr x y₁ y₃ (isomorphic_trans g₁ g₂)
               =
               (fr x y₁ y₂ g₁) @ (fr x y₂ y₃ g₂))
           (fl : forall (x₁ x₂ : C₁) (y : C₂),
               x₁ <~=~> x₂ -> f x₁ y = f x₂ y)
           (fle : forall (x : C₁) (y : C₂),
               fl x x y (isomorphic_refl C₁ x) = idpath)
           (flc : forall (x₁ x₂ x₃ : C₁) (y : C₂)
                         (f₂ : x₂ <~=~> x₃) (f₁ : x₁ <~=~> x₂),
               fl x₁ x₃ y (isomorphic_trans f₁ f₂)
               =
               (fl x₁ x₂ y f₁) @ (fl x₂ x₃ y f₂))
           (fp : forall (x₁ x₂ : C₁) (y₁ y₂ : C₂)
                        (f : x₁ <~=~> x₂) (g : y₁ <~=~> y₂),
               square (fl x₁ x₂ y₂ f)
                      (fr x₁ y₁ y₂ g)
                      (fr x₂ y₁ y₂ g)
                      (fl x₁ x₂ y₁ f)).

  Definition rezk_double_rec' : rezk C₁ -> rezk C₂ -> Y.
  Proof.
    intros x y.
    simple refine (rezk_rec _ _ _ _ _ _ x).
    - exact (fun a => rezk_rec Y (f a) (fr a) (fre a) (frc a) _ y).
    - intros a₁ a₂ g₁ ; simpl.
      simple refine (rezk_ind_set (fun z => _) _ _ _ y).
      + exact (fun b => fl a₁ a₂ b g₁).
      + intros b₁ b₂ g₂.
        apply map_path_over.
        refine (whisker_square idpath _ _ idpath _).
        * symmetry.
          apply rezk_rec_beta_rcleq.
        * symmetry.
          apply rezk_rec_beta_rcleq.
        * exact (fp a₁ a₂ b₁ b₂ g₁ g₂).
    - intros a.
      simple refine (rezk_ind_prop (fun z => _) _ _ y).
      exact (fun b => fle a b).
    - intros a₁ a₂ a₃ g₁ g₂ ; simpl.
      simple refine (rezk_ind_prop (fun z => _) _ _ y).
      exact (fun b => flc a₁ a₂ a₃ b g₁ g₂).
  Defined.

  Definition rezk_double_rec'_beta_l_rcleq
             {x₁ x₂ : C₁} (y : C₂) (g : x₁ <~=~> x₂)
    : ap (fun z => rezk_double_rec' z (rcl C₂ y)) (rcleq C₁ g)
      =
      fl x₁ x₂ y g.
  Proof.
    apply rezk_rec_beta_rcleq.
  Qed.

  Definition rezk_double_rec'_beta_r_rcleq
             (x : C₁) {y₁ y₂ : C₂} (g : y₁ <~=~> y₂)
    : ap (rezk_double_rec' (rcl C₁ x)) (rcleq C₂ g)
      =
      fr x y₁ y₂ g.
  Proof.
    apply (rezk_rec_beta_rcleq C₂).
  Qed.

  Definition rezk_double_rec : rezk C₁ * rezk C₂ -> Y
    := uncurry rezk_double_rec'.

  Definition rezk_double_rec_point (x : C₁) (y : C₂)
    : rezk_double_rec (rcl C₁ x, rcl C₂ y) = f x y
    := idpath.

  Definition rezk_double_rec_beta_rcleq
             {x₁ x₂ : C₁} {y₁ y₂ : C₂}
             (g₁ : x₁ <~=~> x₂) (g₂ : y₁ <~=~> y₂)
    : ap rezk_double_rec (path_prod' (rcleq C₁ g₁) (rcleq C₂ g₂))
      =
      fl x₁ x₂ y₁ g₁ @ fr x₂ y₁ y₂ g₂.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => p @ _) (rezk_rec_beta_rcleq C₁ _ _ _ _ _ _ _) @ _).
    exact (ap (fun p => _ @ p) (rezk_rec_beta_rcleq C₂ _ _ _ _ _ _ _)).
  Qed.

  Definition rezk_double_rec_beta_l_rcleq
             {x₁ x₂ : C₁} (y : C₂) (g : x₁ <~=~> x₂)
    : ap rezk_double_rec (path_prod' (rcleq C₁ g) (idpath : rcl C₂ y = _))
      =
      fl x₁ x₂ y g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => p @ _) (rezk_rec_beta_rcleq C₁ _ _ _ _ _ _ _) @ _).
    apply concat_p1.
  Qed.
  
  Definition rezk_double_rec_beta_r_rcleq
             (x : C₁) {y₁ y₂ : C₂} (g : y₁ <~=~> y₂)
    : ap rezk_double_rec (path_prod' (idpath  : rcl C₁ x = _) (rcleq C₂ g))
      =
      fr x y₁ y₂ g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    refine (ap (fun p => _ @ p) (rezk_rec_beta_rcleq C₂ _ _ _ _ _ _ _) @ _).
    apply concat_1p.
  Qed.
End rezk_double_rec.

Arguments rezk_double_rec {C₁ C₂} Y {_ _}.
Arguments rezk_double_rec' {C₁ C₂} Y {_ _}.
Arguments rezk_double_rec_beta_rcleq {C₁ C₂} Y {_ _}.

(** Double induction over a family of sets.
    We use the same trick as for double recursion.
 *)
Section rezk_double_ind_set.
  Variable (C₁ C₂ : PreCategory)
           (Y : rezk C₁ -> rezk C₂ -> Type).
  Context `{forall (x : rezk C₁) (y : rezk C₂), IsHSet (Y x y)}
          `{Funext}.
  
  Variable (f : forall (x : C₁) (y : C₂), Y (rcl C₁ x) (rcl C₂ y))
           (fr : forall (x : C₁) (y₁ y₂ : C₂) (g : y₁ <~=~> y₂),
               path_over (Y (rcl C₁ x)) (rcleq C₂ g) (f x y₁) (f x y₂))
           (fl : forall (x₁ x₂ : C₁) (y : C₂) (g : x₁ <~=~> x₂),
               path_over (fun z : rezk C₁ => Y z (rcl C₂ y))
                         (rcleq C₁ g)
                         (f x₁ y)
                         (f x₂ y)).
  
  Definition rezk_double_ind_set : forall (x : rezk C₁) (y : rezk C₂), Y x y.
  Proof.
    intros x y.
    simple refine (rezk_ind_set (fun z => _) _ _ _ x).
    - exact (fun a => rezk_ind_set (fun z => _) (f a) (fr a) _ y).
    - intros a₁ a₂ g ; simpl.
      simple refine (rezk_ind_prop (fun z => _) _ _ y).
      exact (fun b => fl a₁ a₂ b g).
  Defined.
End rezk_double_ind_set.

Arguments rezk_double_ind_set {C₁ C₂} Y {_ _}.

(** Double induction over a family of propositions.
    We use the same trick as before.
 *)
Section rezk_double_ind_prop.
  Variable (C₁ C₂ : PreCategory)
           (Y : rezk C₁ -> rezk C₂ -> Type).
  Context `{forall (x : rezk C₁) (y : rezk C₂), IsHProp (Y x y)}
          `{Funext}.
  
  Variable (f : forall (x : C₁) (y : C₂), Y (rcl C₁ x) (rcl C₂ y)).
  
  Definition rezk_double_ind_prop : forall (x : rezk C₁) (y : rezk C₂), Y x y.
  Proof.
    intros x y.
    simple refine (rezk_ind_prop (fun z => _) _ _ x).
    exact (fun a => rezk_ind_prop (fun z => _) (f a) _ y).
  Defined.
End rezk_double_ind_prop.

Arguments rezk_double_ind_prop {C₁ C₂} Y.

(** A special instance of double recursion for defining set-relations.
    This requires univalence, because we need to give equalities in [hSet].
    These equalities are made with [path_hset] and two functions need to be given.
    For the higher coherencies, these functions need to satisfy some laws.
 *)
Section rezk_relation.
  Variable (C₁ C₂ : PreCategory)
           (R : C₁ -> C₂ -> hSet)
           (fl : forall (x₁ x₂ : C₁) (y : C₂), x₁ <~=~> x₂ -> R x₁ y -> R x₂ y)
           (fr : forall (x : C₁) (y₁ y₂ : C₂), y₁ <~=~> y₂ -> R x y₁ -> R x y₂).
  
  Context `{forall (x₁ x₂ : C₁) (y : C₂) (g : x₁ <~=~> x₂), IsEquiv (fl x₁ x₂ y g)}
          `{forall (x : C₁) (y₁ y₂ : C₂) (g : y₁ <~=~> y₂), IsEquiv (fr x y₁ y₂ g)}.
  Context `{Univalence}.

  Variable (fl_id : forall (x : C₁) (y : C₂), fl x x y (isomorphic_refl C₁ x) == idmap)
           (fl_comp : forall (x₁ x₂ x₃ : C₁) (y : C₂)
                             (g₂ : x₂ <~=~> x₃) (g₁ : x₁ <~=~> x₂),
               fl x₁ x₃ y (isomorphic_trans g₁ g₂) == fl x₂ x₃ y g₂ o (fl x₁ x₂ y g₁))
           (fr_id : forall (x : C₁) (y : C₂), fr x y y (isomorphic_refl C₂ y) == idmap)
           (fr_comp : forall (x : C₁) (y₁ y₂ y₃ : C₂)
                             (g₂ : y₂ <~=~> y₃) (g₁ : y₁ <~=~> y₂),
               fr x y₁ y₃ (isomorphic_trans g₁ g₂) == fr x y₂ y₃ g₂ o (fr x y₁ y₂ g₁))
           (fc : forall (x₁ x₂ : C₁) (y₁ y₂ : C₂)
                        (g₁ : x₁ <~=~> x₂) (g₂ : y₁ <~=~> y₂),
               fl x₁ x₂ y₂ g₁ o fr x₁ y₁ y₂ g₂
               ==
               fr x₂ y₁ y₂ g₂ o fl x₁ x₂ y₁ g₁
           ).

  Definition path_hset_fr_refl
             (a : C₁) (b : C₂)
    : path_hset (BuildEquiv _ _ (fr a b b (isomorphic_refl C₂ b)) _) = idpath.
  Proof.
    refine (_ @ path_trunctype_1).
    apply path_trunctype_eq ; cbn.
    apply fr_id.
  Qed.

  Definition path_hset_fr_trans
             (a : C₁) (b₁ b₂ b₃ : C₂)
             (g₁ : b₂ <~=~> b₃) (g₂ : b₁ <~=~> b₂)
    : path_hset (BuildEquiv _ _ (fr a b₁ b₃ (isomorphic_trans g₂ g₁)) _)
      =
      (path_hset (BuildEquiv _ _ (fr a b₁ b₂ g₂) _))
        @
        path_hset (BuildEquiv _ _ (fr a b₂ b₃ g₁) _).
  Proof.
    refine (_ @ path_trunctype_pp _ _).
    apply path_trunctype_eq ; cbn.
    apply fr_comp.
  Qed.

  Definition path_hset_fl_refl
             (a : C₁) (b : C₂)
    : path_hset (BuildEquiv _ _ (fl a a b (isomorphic_refl C₁ a)) _) = idpath.
  Proof.
    refine (_ @ path_trunctype_1).
    apply path_trunctype_eq ; cbn.
    apply fl_id.
  Qed.
  
  Definition path_hset_fl_trans
             (a₁ a₂ a₃ : C₁) (b : C₂)
             (g₁ : a₂ <~=~> a₃) (g₂ : a₁ <~=~> a₂)
    : path_hset (BuildEquiv _ _ (fl a₁ a₃ b (isomorphic_trans g₂ g₁)) _)
      =
      (path_hset (BuildEquiv _ _ (fl a₁ a₂ b g₂) _))
        @
        path_hset (BuildEquiv _ _ (fl a₂ a₃ b g₁) _).
  Proof.
    refine (_ @ path_trunctype_pp _ _).
    apply path_trunctype_eq ; cbn.
    apply fl_comp.
  Qed.

  Definition path_hset_fl_fr
             (a₁ a₂ : C₁) (b₁ b₂ : C₂)
             (g₁ : a₁ <~=~> a₂)
             (g₂ : b₁ <~=~> b₂)
    : (path_hset (BuildEquiv _ _ (fr a₁ b₁ b₂ g₂) _))
        @
        path_hset (BuildEquiv _ _ (fl a₁ a₂ b₂ g₁) _)
      =
      (path_hset (BuildEquiv _ _ (fl a₁ a₂ b₁ g₁) _))
        @
        path_hset (BuildEquiv _ _ (fr a₂ b₁ b₂ g₂) _).
  Proof.
    refine ((path_trunctype_pp _ _)^ @ _ @ path_trunctype_pp _ _).
    apply path_trunctype_eq ; cbn.
    apply fc.
  Qed.

  Definition rezk_relation : rezk C₁ -> rezk C₂ -> hSet.
  Proof.
    simple refine (rezk_double_rec' _ _ _ _ _ _ _ _).
    - exact R.
    - exact (fun a b₁ b₂ g => path_hset (BuildEquiv _ _ (fr a b₁ b₂ g) _)).
    - exact path_hset_fr_refl.
    - exact path_hset_fr_trans.
    - exact (fun a₁ a₂ b g => path_hset (BuildEquiv _ _ (fl a₁ a₂ b g) _)).
    - exact path_hset_fl_refl.
    - exact path_hset_fl_trans.
    - intros a₁ a₂ b₁ b₂ g₁ g₂.
      apply path_to_square.
      apply path_hset_fl_fr.
  Defined.

  Definition rezk_relation_rcl_rcl (x : C₁) (y : C₂)
    : rezk_relation (rcl C₁ x) (rcl C₂ y) = R x y
    := idpath.

  Definition rezk_relation_beta_l_rcleq
             {x₁ x₂ : C₁} (y : C₂) (g : x₁ <~=~> x₂)
    : ap (fun z => rezk_relation z (rcl C₂ y)) (rcleq C₁ g)
      =
      path_hset (BuildEquiv _ _ (fl x₁ x₂ y g) _).
  Proof.
    exact (rezk_double_rec'_beta_l_rcleq C₁ C₂ hSet R _ _ _ _ _ _ _ _ g).
  Qed.

  Definition rezk_relation_beta_r_rcleq
             (x : C₁) {y₁ y₂ : C₂} (g : y₁ <~=~> y₂)
    : ap (rezk_relation (rcl C₁ x)) (rcleq C₂ g)
      =
      path_hset (BuildEquiv _ _ (fr x y₁ y₂ g) _).
  Proof.
    exact (rezk_double_rec'_beta_r_rcleq C₁ C₂ hSet R _ _ _ _ _ _ _ _ g).
  Qed.
End rezk_relation.