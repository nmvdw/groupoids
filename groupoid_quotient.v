Require Import HoTT.
From GR Require Import groupoid path_over globe_over.

Definition uncurry
           {X Y Z : Type}
           (f : X -> Y -> Z)
  : X * Y -> Z
  := fun p => f (fst p) (snd p).

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

Module Export gquot.
  Private Inductive gquot {A : Type} (G : groupoid A) :=
  | gcl : A -> gquot G.

  Arguments gcl {_} _ _.

  Axiom geqcl
    : forall {A : Type} (G : groupoid A) {a₁ a₂ : A} (g : hom G a₁ a₂),
      gcl G a₁ = gcl G a₂.

  Axiom ge
    : forall {A : Type} (G : groupoid A) (a : A),
      geqcl G (e a) = idpath.

  Axiom ginv
    : forall {A : Type} (G : groupoid A) {a₁ a₂ : A} (g : hom G a₁ a₂),
      geqcl G (inv g) = (geqcl G g)^.

  Axiom gconcat
    : forall {A : Type} (G : groupoid A)
             {a₁ a₂ a₃ : A}
             (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
      geqcl G (g₁ × g₂) = geqcl G g₁ @ geqcl G g₂.
  
  Axiom gtrunc
    : forall {A : Type} (G : groupoid A), IsTrunc 1 (gquot G).

  Section gquot_ind.
    Variable (A : Type)
             (G : groupoid A)
             (Y : gquot G -> Type)
             (gclY : forall (a : A), Y(gcl G a))
             (geqclY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 path_over Y (geqcl G g) (gclY a₁) (gclY a₂))
             (geY : forall (a : A), globe_over Y
                                                (path_to_globe (ge G a))
                                                (geqclY a a (e a))
                                                (path_over_id (gclY a)))
             (ginvY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 globe_over Y
                            (path_to_globe (ginv G g))
                            (geqclY a₂ a₁ (inv g))
                            (path_over_inv (geqclY a₁ a₂ g)))
             (gconcatY : forall (a₁ a₂ a₃ : A)
                                (g₁ : hom G a₁ a₂) (g₂ : hom G a₂ a₃),
                 globe_over Y
                            (path_to_globe (gconcat G g₁ g₂))
                            (geqclY a₁ a₃ (g₁ × g₂))
                            (path_over_concat (geqclY a₁ a₂ g₁)
                                              (geqclY a₂ a₃ g₂)))
             (truncY : forall (x : gquot G), IsTrunc 1 (Y x)).

    Fixpoint gquot_ind (g : gquot G) : Y g
      := (match g with
         | gcl a => fun _ _ _ _ _ => gclY a
          end) geqclY geY ginvY gconcatY truncY.

    Axiom gquot_ind_beta_geqcl : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
        apd_po gquot_ind (geqcl G g)
        =
        geqclY a₁ a₂ g.
  End gquot_ind.

  Section gquot_rec.
    Variable (A : Type)
             (G : groupoid A)
             (Y : Type)
             (gclY : A -> Y)
             (geqclY : forall (a₁ a₂ : A),
                 hom G a₁ a₂ -> gclY a₁ = gclY a₂)
             (geY : forall (a : A), geqclY _ _ (e a) = idpath)
             (ginvY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 geqclY a₂ a₁ (inv g) = (geqclY a₁ a₂ g)^)
             (gconcatY : forall (a₁ a₂ a₃: A) (g₁: hom G a₁ a₂) (g₂: hom G a₂ a₃),
                 geqclY _ _ (g₁ × g₂) = geqclY _ _ g₁ @ geqclY _ _ g₂)
             (truncY : IsTrunc 1 Y).

    Definition gquot_rec : gquot G -> Y.
    Proof.
      simple refine (gquot_ind A G (fun _ => Y)
                               gclY
                               (fun a₁ a₂ g => const_path_over (geqclY a₁ a₂ g))
                               (fun a => const_globe_over
                                           (path_to_globe (ge G a))
                                           (geqclY a a (e a))
                                           idpath
                                           (path_to_globe (geY a)))
                               _ _ _) ; cbn.
      - intros a₁ a₂ g.
        simple refine (globe_over_whisker
                         (fun _ => Y)
                         _
                         idpath
                         (const_path_over_inv _)
                         (const_globe_over
                            (path_to_globe (ginv G g))
                            (geqclY a₂ a₁ (inv g))
                            ((geqclY a₁ a₂ g)^)
                            (path_to_globe (ginvY a₁ a₂ g))
                         )
                      ).
      - intros a₁ a₂ a₃ g₁ g₂.
        simple refine (globe_over_whisker
                         (fun _ => Y)
                         _
                         idpath
                         (const_path_over_concat _ _)
                         (const_globe_over
                            (path_to_globe (gconcat G g₁ g₂))
                            (geqclY a₁ a₃ (g₁ × g₂))
                            (geqclY a₁ a₂ g₁ @ geqclY a₂ a₃ g₂)
                            (path_to_globe (gconcatY a₁ a₂ a₃ g₁ g₂))
                         )
                      ).
    Defined.

    Definition gquot_rec_beta_geqcl (a₁ a₂ : A) (g : hom G a₁ a₂)
      : ap gquot_rec (geqcl G g) = geqclY a₁ a₂ g.
    Proof.
      apply (const_path_over_inj (geqcl G g)).
      refine ((apd_po_const _ _)^ @ _).
      apply gquot_ind_beta_geqcl.
    Defined.
  End gquot_rec.

  Section gquot_ind_set.
    Variable (A : Type)
             (G : groupoid A)
             (Y : gquot G -> Type)
             (gclY : forall (a : A), Y(gcl G a))
             (geqclY : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
                 path_over Y (geqcl G g) (gclY a₁) (gclY a₂))
             (truncY : forall (x : gquot G), IsHSet (Y x)).

    Definition gquot_ind_set : forall (g : gquot G), Y g.
    Proof.
      simple refine (gquot_ind A G Y gclY geqclY _ _ _ _)
      ; intros ; apply path_to_globe_over ; apply path_ishprop.
    Defined.

    Definition gquot_ind_set_beta_geqcl : forall (a₁ a₂ : A) (g : hom G a₁ a₂),
        apd_po gquot_ind_set (geqcl G g)
        =
        geqclY a₁ a₂ g.
    Proof.
      apply gquot_ind_beta_geqcl.
    Defined.
  End gquot_ind_set.

  Section gquot_ind_prop.
    Variable (A : Type)
             (G : groupoid A)
             (Y : gquot G -> Type)
             (gclY : forall (a : A), Y(gcl G a))
             (truncY : forall (x : gquot G), IsHProp (Y x)).

    Definition gquot_ind_prop : forall (g : gquot G), Y g.
    Proof.
      simple refine (gquot_ind_set A G Y gclY _ _)
      ; intros ; apply path_to_path_over ; apply path_ishprop.
    Defined.
  End gquot_ind_prop.
End gquot.

Arguments gquot_ind {A G} Y gclY geqclY geY ginvY gconcatY truncY.
Arguments gquot_ind_set {A G} Y gclY geqclY truncY.
Arguments gquot_ind_prop {A G} Y gclY truncY.
Arguments gquot_rec {A G}.

Section gquot_double_rec.
  Variable (A B : Type)
           (G₁ : groupoid A)
           (G₂ : groupoid B)
           (Y : Type).
  Context `{IsTrunc 1 Y}
          `{Funext}.

  Variable (f : A -> B -> Y)
           (fr : forall (a : A) (b₁ b₂ : B), hom G₂ b₁ b₂ -> f a b₁ = f a b₂)
           (fre : forall (a : A) (b : B), fr a b b (e b) = idpath)
           (fri : forall (a : A) (b₁ b₂ : B) (g : hom G₂ b₁ b₂),
               fr a b₂ b₁ (inv g) = (fr a b₁ b₂ g)^)
           (frc : forall (a : A) (b₁ b₂ b₃ : B)
                         (g₁ : hom G₂ b₁ b₂) (g₂ : hom G₂ b₂ b₃),
               fr a b₁ b₃ (g₁ × g₂)
               =
               (fr a b₁ b₂ g₁) @ (fr a b₂ b₃ g₂))
           (fl : forall (a₁ a₂ : A) (b : B), hom G₁ a₁ a₂ -> f a₁ b = f a₂ b)
           (fle : forall (a : A) (b : B), fl a a b (e a) = idpath)
           (fli : forall (a₁ a₂ : A) (b : B) (g : hom G₁ a₁ a₂),
               fl a₂ a₁ b (inv g) = (fl a₁ a₂ b g)^)
           (flc : forall (a₁ a₂ a₃ : A) (b : B)
                         (g₁ : hom G₁ a₁ a₂) (g₂ : hom G₁ a₂ a₃),
               fl a₁ a₃ b (g₁ × g₂)
               =
               (fl a₁ a₂ b g₁) @ (fl a₂ a₃ b g₂))
           (fp : forall (a₁ a₂ : A) (b₁ b₂ : B)
                        (g₁ : hom G₁ a₁ a₂) (g₂ : hom G₂ b₁ b₂),
              ((ap (gquot_rec Y (f a₁) (fr a₁) (fre a₁) (fri a₁) (frc a₁) H)
                   (geqcl G₂ g₂))^)
                @ (fl a₁ a₂ b₁ g₁)
                @ (ap (gquot_rec Y (f a₂) (fr a₂) (fre a₂) (fri a₂) (frc a₂) H)
                      (geqcl G₂ g₂))
              = 
              fl a₁ a₂ b₂ g₁).

  Definition gquot_double_rec' : gquot G₁ -> gquot G₂ -> Y.
  Proof.
    intros x y.
    simple refine (gquot_rec _ _ _ _ _ _ _ x).
    - exact (fun a => gquot_rec Y (f a) (fr a) (fre a) (fri a) (frc a) _ y).
    - intros a₁ a₂ g₁ ; simpl.
      simple refine (gquot_ind_set (fun z => _) _ _ _ y).
      + exact (fun b => fl a₁ a₂ b g₁).
      + intros b₁ b₂ g₂.
        apply path_to_path_over.
        exact (transport_paths_FlFr _ _ @ fp a₁ a₂ b₁ b₂ g₁ g₂).
    - intros a ; cbn.
      simple refine (gquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => fle a b).
    - intros a₁ a₂ g ; cbn.
      simple refine (gquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => fli a₁ a₂ b g).
    - intros a₁ a₂ a₃ g ; cbn.
      simple refine (gquot_ind_prop (fun z => _) _ _ y).
      exact (fun b => flc a₁ a₂ a₃ b g).
  Defined.

  Definition gquot_double_rec : gquot G₁ * gquot G₂ -> Y
    := uncurry gquot_double_rec'.

  Definition gquot_double_rec_point (a : A) (b : B)
    : gquot_double_rec (gcl G₁ a, gcl G₂ b) = f a b
    := idpath.

  Definition gquot_double_rec_beta_gcleq
             {a₁ a₂ : A} {b₁ b₂ : B}
             (g₁ : hom G₁ a₁ a₂) (g₂ : hom G₂ b₁ b₂)
    : ap gquot_double_rec (path_prod' (geqcl G₁ g₁) (geqcl G₂ g₂))
      =
      fl a₁ a₂ b₁ g₁ @ fr a₂ b₁ b₂ g₂.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    unfold gquot_double_rec' ; simpl.
    rewrite !gquot_rec_beta_geqcl.
    reflexivity.
  Defined.

  Definition gquot_double_rec_beta_l_gcleq
             {a₁ a₂ : A} (b : B) (g : hom G₁ a₁ a₂)
    : ap gquot_double_rec (path_prod' (geqcl G₁ g) (idpath : gcl G₂ b = _))
      =
      fl a₁ a₂ b g.
  Proof.
    refine (uncurry_ap _ _ _ @ _).
    unfold gquot_double_rec' ; simpl.
    rewrite !gquot_rec_beta_geqcl.
    apply concat_p1.
  Defined.

  Definition gquot_double_rec_beta_r_gcleq
             (a : A) {b₁ b₂ : B} (g : hom G₂ b₁ b₂)
    : ap gquot_double_rec (path_prod' (idpath  : gcl G₁ a = _) (geqcl G₂ g))
      =
      fr a b₁ b₂ g.
  Proof.
    rewrite uncurry_ap.
    unfold gquot_double_rec' ; simpl.
    rewrite !gquot_rec_beta_geqcl.
    apply concat_1p.
  Defined.
End gquot_double_rec.