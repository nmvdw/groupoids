Require Import HoTT.
From GR Require Import general path_over globe_over square.
From GR Require Export groupoid_quotient.

(**  gquot is a left adjoint to the path groupoid construction.
     Furthermore, this adjunction is actually a reflection exhibiting path_groupoid is an inclusion of 1-Types into groupoids. *)
Section adjunction.
  Context `{Univalence}.

  (** ** The path groupoid functor *)
  Definition path_groupoid (A : TruncType 1) : groupoid A
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

  Definition path_groupoid_functor {A B : TruncType 1} (f : A -> B) :
    groupoid_functor (path_groupoid A) (path_groupoid B).
  Proof.
    simple refine (Build_groupoid_functor _ _ _ _ f _ _ _ _).
    - simpl. refine (fun x y p => ap f p).
    - intros x ; simpl ; reflexivity.
    - intros x y g ; simpl. apply ap_V.
    - intros x y z g₁ g₂ ; simpl. apply ap_pp.
  Defined.

  (** ** The groupoid quotient functor (free 1-type) *)
  Definition gquot' {A : TruncType 1} (G : groupoid A) : TruncType 1 :=
    BuildTruncType 1 (gquot G).

  Definition gquot'_functor {A B : TruncType 1} {G₁ : groupoid A} {G₂ : groupoid B}
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

  (** ** Counit of the adjunction is an isomorphism *)
  Definition counit (A : TruncType 1) : gquot (path_groupoid A) -> A.
  Proof.
    simple refine (gquot_rec A idmap _ _ _ _ _) ; cbn.
    - exact (fun _ _ => idmap).
    - exact (fun _ => idpath).
    - exact (fun _ _ _ => idpath).
    - exact (fun _ _ _ _ _ => idpath).
  Defined.

  Definition path_over_help
             {A : TruncType 1}
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
  Definition unit_obj {A : TruncType 1} (G : groupoid A) : A -> (gquot' G) :=  gcl _.
  Definition unit_hom {A : TruncType 1} {G : groupoid A} {x y : A}
             (g : hom G x y) : hom (path_groupoid (gquot' G)) (unit_obj G x) (unit_obj G y) := gcleq _ g.
  Definition unit_hom_e {A : TruncType 1} {G : groupoid A} (x : A) : unit_hom (e x) = e (unit_obj G x).
  Proof. simpl. apply ge. Defined.
  Definition unit_hom_inv {A : TruncType 1} {G : groupoid A} {x y : A}
             (g : hom G x y) : unit_hom (inv g) = inv (unit_hom g).
  Proof. simpl. apply ginv. Defined.
  Definition unit_hom_concat {A : TruncType 1} {G : groupoid A} {x y z : A}
             (g₁ : hom G x y) (g₂ : hom G y z) : unit_hom (g₁ × g₂) = ((unit_hom g₁) × (unit_hom g₂)).
  Proof. simpl. apply gconcat. Defined.

  Definition unit {A : TruncType 1} (G : groupoid A) : groupoid_functor G (path_groupoid (gquot' G)) :=
    {| f_obj := unit_obj G;
       f_hom := fun x y g => unit_hom g;
       f_e := unit_hom_e;
       f_inv := fun x y g => unit_hom_inv g;
       f_comp := fun x y z g₁ g₂ => unit_hom_concat g₁ g₂
     |}.

  (** ** Unit-counit equations for an adjunction *)
  Lemma counit_unit {A : TruncType 1} :
    functor_comp (unit (path_groupoid A)) (path_groupoid_functor (counit A)) = idfunctor (path_groupoid A).
  Proof.
    simple refine (functor_eq _ _ _ _); simpl.
    - exact idpath.
    - funext x y g.  compute[unit_hom counit].
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ _ _).
  Defined.

  Lemma unit_counit {A : TruncType 1} (G : groupoid A) :
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

End adjunction.
