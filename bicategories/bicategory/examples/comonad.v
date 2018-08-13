Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     examples.terminal
     examples.precat
     examples.oplax_functors_bicat.
From GR.bicategories.lax_functor Require Import
     lax_functor
     oplax_functor.
From GR.bicategories.lax_transformation Require Import
     lax_transformation.
From GR.bicategories.modification Require Import
     modification.

Section CoMonad.
  Context `{Funext}.
  Variable (C : BiCategory).

  Definition comonad := OpLax terminal_bicategory C.

  Section CoMonadData.
    Variable (m : comonad).
    
    Definition under_c :  C
      := Fobj m tt.

    Definition endo_c : C⟦under_c,under_c⟧
      := m ₁ tt.

    Definition extend : endo_c ==> id₁ under_c
      := Fid m tt.

    Definition duplicate : endo_c ==> endo_c · endo_c
      := @Fcomp₁ _ _ m tt tt tt tt tt.

    Definition extend_duplicate
      : left_unit endo_c ∘ (extend ◅ endo_c) ∘ duplicate
        =
        id₂ endo_c.
    Proof.
      unfold duplicate, extend, endo_c, bc_whisker_l ; cbn.
      rewrite <- left_unit_left.
      rewrite !vcomp_assoc.
      f_ap.
      rewrite left_unit_left.
      rewrite opF_left_unit.      
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.

    Definition duplicate_extend
      : right_unit endo_c ∘ (endo_c ▻ extend) ∘ duplicate
        =
        id₂ endo_c.
    Proof.
      unfold duplicate, extend, endo_c, bc_whisker_l ; cbn.
      rewrite <- right_unit_left.
      rewrite !vcomp_assoc.
      f_ap.
      rewrite opF_right_unit.      
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.

    Definition duplicate_duplicate
      : (duplicate ◅ endo_c) ∘ duplicate
        =
        assoc_inv endo_c endo_c endo_c ∘ (endo_c ▻ duplicate) ∘ duplicate.
    Proof.
      unfold duplicate, extend, endo_c, bc_whisker_l, bc_whisker_r ; cbn.
      rewrite !vcomp_assoc.
      pose (@opF_assoc terminal_bicategory C m tt tt tt tt tt tt tt).
      simpl in p.
      refine (_ @ p^).
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity ; simpl.
      reflexivity.
    Qed.
  End CoMonadData.

  Definition comonad_morphism (m₁ m₂ : comonad)
    := comonad⟦m₁,m₂⟧.

  Section MorphismData.
    Context {m₁ m₂ : comonad}.
    Variable (η : comonad_morphism m₁ m₂).

    Definition under_cm : C⟦under_c m₁,under_c m₂⟧
      := laxcomponent_of η tt.

    Definition under_cm_natural
      : under_cm · endo_c m₁ ==> endo_c m₂ · under_cm
      := laxnaturality_of η tt.

    Definition under_cm_extend
      : extend m₂ * id₂ under_cm ∘ under_cm_natural
        =
        left_unit_inv under_cm ∘ (right_unit under_cm ∘ (id₂ under_cm * extend m₁))
      := transformation_unit η tt.

    Definition under_cm_duplicate
      : duplicate m₂ * id₂ under_cm ∘ under_cm_natural
        =
        (assoc_inv (endo_c m₂) (endo_c m₂) under_cm)
          ∘ ((id₂ (endo_c m₂) * under_cm_natural)
               ∘ (assoc (endo_c m₂) under_cm (endo_c m₁)
                   ∘ ((under_cm_natural * id₂ (endo_c m₁))
                        ∘ (assoc_inv under_cm (endo_c m₁) (endo_c m₁)
                                     ∘ (id₂ under_cm * duplicate m₁)))))
      := @transformation_assoc _ _ _ _ η tt tt tt tt tt.
  End MorphismData.

  Definition comonad_transformation
             {m₁ m₂ : comonad}
             (η₁ η₂ : comonad_morphism m₁ m₂)
    := η₁ ==> η₂.

  Section TransformationData.
    Context {m₁ m₂ : comonad}
            {η₁ η₂ : comonad_morphism m₁ m₂}.
    Variable (σ : comonad_transformation η₁ η₂).

    Definition under_cmm : under_cm η₂ ==> under_cm η₁
      := mod_component σ tt.

    Definition under_mmm_natural
      : (endo_c m₂ ▻ under_cmm) ∘ under_cm_natural η₂
        =
        under_cm_natural η₁ ∘ (under_cmm ◅ endo_c m₁)
      := mod_commute σ tt.
  End TransformationData.  
End CoMonad.