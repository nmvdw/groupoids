Require Import HoTT.
From GR Require Import general path_over globe_over square.
From GR Require Export groupoid_quotient.

(**  gquot is a left adjoint to the path groupoid construction.
     Furthermore, this adjunction is actually a reflection exhibiting path_groupoid is an inclusion of 1-Types into groupoids. *)
Section adjunction.
  Context `{Univalence}.

  (** ** The path groupoid functor *)
  Definition path_groupoid (A : 1-Type) : groupoid A
    := {|hom := fun x y => BuildhSet(x = y) ;
         e := fun _ => idpath ;
         inv := fun _ _ => inverse ;
         comp := fun _ _ _ => concat ;
         ca := fun _ _ _ _ => concat_p_pp ;
         ce := fun _ _ => concat_p1 ;
         ec := fun _ _ => concat_1p ;
         ci := fun _ _ => concat_pV ;
         ic := fun _ _ => concat_Vp
       |}.

  Definition path_groupoid_functor {A B : 1-Type} (f : A -> B) :
    groupoid_functor (path_groupoid A) (path_groupoid B).
  Proof.
    simple refine (Build_groupoid_functor _ _ _ _ f _ _ _ _).
    - simpl. refine (fun x y p => ap f p).
    - intros x ; simpl ; reflexivity.
    - intros x y g ; simpl. apply ap_V.
    - intros x y z g₁ g₂ ; simpl. apply ap_pp.
  Defined.

  Lemma path_groupoid_functor_1 {A : 1-Type} :
    path_groupoid_functor (fun x : A => x) = (idfunctor (path_groupoid A)).
  Proof.
    simple refine (functor_eq _ _ _ _).
    - reflexivity.
    - simpl. funext x y p. apply ap_idmap.
  Defined.

  Lemma path_groupoid_functor_compose {A B C : 1-Type}
        (f : A -> B) (g : B -> C) :
    path_groupoid_functor (g o f) = functor_comp (path_groupoid_functor f) (path_groupoid_functor g).
  Proof.
    simple refine (functor_eq _ _ _ _).
    - reflexivity.
    - simpl. funext x y p. apply ap_compose.
  Defined.

  (** ** The groupoid quotient functor (free 1-type) *)
  Definition gquot' {A : 1-Type} (G : groupoid A) : 1-Type :=
    BuildTruncType 1 (gquot G).

  Definition gquot'_functor {A B : 1-Type} {G₁ : groupoid A} {G₂ : groupoid B}
             (f : groupoid_functor G₁ G₂) : gquot G₁ -> gquot G₂.
  Proof.
    simple refine (gquot_rec _ _ _ _ _ _ _).
    - intros x. refine (gcl _ (f_obj f x)).
    - intros x y g ; simpl. apply gcleq.
      apply (f_hom f). exact g.
    - intros x ; simpl.
      refine (_ @ ge _ _).
      refine (ap (gcleq _) (f_e _)).
    - intros x y g ; simpl.
      refine (_ @ ginv _ _).
      refine (ap (gcleq _) (f_inv _ _ _)).
    - intros x y z g₁ g₂ ; simpl.
      refine (_ @ gconcat _ _ _).
      refine (ap (gcleq _) (f_comp _ _ _ _ _)).
  Defined.

  Lemma gquot'_functor_compose {A B C : 1-Type}
        {G₁ : groupoid A} {G₂ : groupoid B} {G₃ : groupoid C}
        (f : groupoid_functor G₁ G₂) (g : groupoid_functor G₂ G₃) :
    gquot'_functor (functor_comp f g) = gquot'_functor g o gquot'_functor f.
  Proof.
    apply path_forall.
    simple refine (gquot_ind_set _ _ _ _).
    - intros a. simpl. reflexivity.
    - intros a₁ a₂ h. simpl.
      apply map_path_over.
      refine (whisker_square idpath _ _ idpath (vrefl _)).
      + rewrite gquot_rec_beta_gcleq. reflexivity.
      + rewrite ap_compose.
        do 2 rewrite gquot_rec_beta_gcleq. reflexivity.
  Qed.

  (** ** Counit of the adjunction is an isomorphism *)
  Definition counit (A : 1-Type) : gquot (path_groupoid A) -> A.
  Proof.
    simple refine (gquot_rec A idmap _ _ _ _ _) ; cbn.
    - exact (fun _ _ => idmap).
    - exact (fun _ => idpath).
    - exact (fun _ _ _ => idpath).
    - exact (fun _ _ _ _ _ => idpath).
  Defined.

  Lemma counit_nat {A B : 1-Type} (f : A -> B) :
    f o counit A = counit B o (gquot'_functor (path_groupoid_functor f)).
  Proof.
    apply path_forall.
    simple refine (gquot_ind_set _ _ _ _).
    - intros a. simpl. reflexivity.
    - intros a₁ a₂ h. simpl.
      apply map_path_over.
      refine (whisker_square idpath _ _ idpath (vrefl _)).
      + rewrite ap_compose.
        rewrite gquot_rec_beta_gcleq.
        reflexivity.
      + rewrite (ap_compose (gquot'_functor (path_groupoid_functor f))).
        do 2 rewrite gquot_rec_beta_gcleq.
        reflexivity.
  Qed.

  Definition path_over_help
             {A : 1-Type}
             {a₁ a₂ : A}
             (g : hom (path_groupoid A) a₁ a₂)
    : path_over (fun z : gquot _ => gcl _ (counit _ z) = z)
                (gcleq _ g)
                idpath
                idpath.
  Proof.
    apply map_path_over.
    induction g ; cbn.
    refine (whisker_square idpath _ _ idpath _).
    - refine (ap_compose _ _ _ @ ap _ _)^.
      apply gquot_rec_beta_gcleq.
    - refine (ap_idmap _ @ _)^.
      apply ge.
    - exact id_square.
  Defined.

  Global Instance counit_isequiv A : IsEquiv (counit A).
  Proof.
    simple refine (isequiv_adjointify _ (gcl _) _ _).
    - intros x ; reflexivity.
    - intros x.
      simple refine (gquot_ind_set (fun z => _) _ _ _ x).
      + intros a ; cbn.
        reflexivity.
      + intros.
        apply path_over_help.
   Defined.

  (** ** Unit reflects groupoids into types *)
  Definition unit_obj {A : 1-Type} (G : groupoid A) : A -> (gquot' G) :=  gcl _.
  Definition unit_hom {A : 1-Type} {G : groupoid A} {x y : A}
             (g : hom G x y) : hom (path_groupoid (gquot' G)) (unit_obj G x) (unit_obj G y) := gcleq _ g.
  Definition unit_hom_e {A : 1-Type} {G : groupoid A} (x : A) : unit_hom (e x) = e (unit_obj G x).
  Proof. simpl. apply ge. Defined.
  Definition unit_hom_inv {A : 1-Type} {G : groupoid A} {x y : A}
             (g : hom G x y) : unit_hom (inv g) = inv (unit_hom g).
  Proof. simpl. apply ginv. Defined.
  Definition unit_hom_concat {A : 1-Type} {G : groupoid A} {x y z : A}
             (g₁ : hom G x y) (g₂ : hom G y z) : unit_hom (g₁ × g₂) = ((unit_hom g₁) × (unit_hom g₂)).
  Proof. simpl. apply gconcat. Defined.

  Definition unit {A : 1-Type} (G : groupoid A) : groupoid_functor G (path_groupoid (gquot' G)) :=
    {| f_obj := unit_obj G;
       f_hom := fun x y g => unit_hom g;
       f_e := unit_hom_e;
       f_inv := fun x y g => unit_hom_inv g;
       f_comp := fun x y z g₁ g₂ => unit_hom_concat g₁ g₂
     |}.

  Lemma unit_nat {A B : 1-Type} {G₁ : groupoid A} {G₂ : groupoid B}
        (g : groupoid_functor G₁ G₂) :
    functor_comp g (unit G₂) =
    functor_comp (unit G₁) (path_groupoid_functor (gquot'_functor g)).
  Proof.
    simple refine (functor_eq _ _ _ _).
    - reflexivity.
    - simpl. funext x y p. unfold unit_hom, f_hom.
      symmetry. refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _ _).
  Defined.

  (** ** Unit-counit equations for an adjunction *)
  Lemma counit_unit {A : 1-Type} :
    functor_comp (unit (path_groupoid A)) (path_groupoid_functor (counit A)) = idfunctor (path_groupoid A).
  Proof.
    simple refine (functor_eq _ _ _ _); simpl.
    - exact idpath.
    - funext x y g.  compute[unit_hom counit].
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _ _).
  Defined.

  Lemma unit_counit {A : 1-Type} (G : groupoid A) :
    (counit (gquot' G)) o (gquot'_functor (unit G)) = idmap.
  Proof.
    apply path_forall. intros x.
    simple refine (gquot_ind_set (fun x => counit (gquot' G) (gquot'_functor (unit G) x) = x) _ _ _ _).
    - intros a. simpl. reflexivity.
    - intros a₁ a₂ g. simpl.
      apply map_path_over.
      refine (whisker_square idpath _ _ idpath (vrefl (gcleq _ g))).
      + rewrite ap_compose.
        do 2 rewrite gquot_rec_beta_gcleq. cbn.
        reflexivity.
      + symmetry. apply ap_idmap.
  Defined.

  (** ** Hom-set bijection formulation *)
  Definition phi {A : 1-Type} (G : groupoid A) (B : 1-Type) :
    (gquot' G -> B) -> (groupoid_functor G (path_groupoid B)) :=
    fun f => functor_comp (unit G) (path_groupoid_functor f).

  Definition phi_i {A : 1-Type} (G : groupoid A) (B : 1-Type) :
    (groupoid_functor G (path_groupoid B)) -> (gquot' G -> B) :=
    fun g => counit B o gquot'_functor g.

  Global Instance phi_isequiv {A : 1-Type} (G : groupoid A) (B : 1-Type) :
    IsEquiv (phi G B).
  Proof.
    simple refine (isequiv_adjointify _ (phi_i G B) _ _).
    - intros g. unfold phi, phi_i.
      rewrite path_groupoid_functor_compose.
      rewrite functor_comp_assoc.
      rewrite <- (unit_nat g).
      rewrite <- functor_comp_assoc.
      rewrite counit_unit.
      apply functor_comp_id_r.
    - intros f. unfold phi, phi_i.
      rewrite gquot'_functor_compose.
      funext x.
      rewrite (apD10 (counit_nat f)^ (gquot'_functor (unit G) x)).
      f_ap.
      apply (apD10 (unit_counit G) x).
  Qed.

  Definition hom_set_iso {A : 1-Type} (G : groupoid A) (B : 1-Type) :
    (gquot' G -> B) <~> (groupoid_functor G (path_groupoid B)) :=
    BuildEquiv _ _ (phi G B) _.

  Definition hom_set_eq {A : 1-Type} (G : groupoid A) (B : 1-Type) :
    (gquot' G -> B) = (groupoid_functor G (path_groupoid B)) :=
    path_universe (phi G B).

End adjunction.
