# groupoids

In basics: cubical methods (heterogeneous equality, globe_over, path_over, square), polynomials (polynomial), general facts (general).
In bicategories.bicategory: definition (bicategory, strict), equivalences in bicategories (equivalence), examples (the bicategory of 1-types, every 2-type is a bicategory, the bicategory of categories, full sub bicategory, opposite bicategory)
In bicategories.lax_functor: definition (lax_functor), examples (a map between 2-types gives a lax functor)
In bicategoriese.lax_transformation: definition (lax_transformation)
In setoid: basic definitions (setoid), properties of the quotient (squot_properties), squot is an adjuction (setoid_adjunction)
In groupoid.grpd_bicategory: definition of groupoids, proof that it is a bicategory, several constructions, laws of groupoids
In groupoid.path_groupoid: every 1-type gives a groupoid via the path space, every type gives a groupoid by truncating the path space.
In groupoid.groupoid_quotient: definition of groupoid quotient (gquot), recursion principles (gquot_principles), functoriality (gquot_functor), in properties the encode-decode proof, it commutes with + and * and general properties are given


Known to compile with the HoTT library version [d79a5b50196a0c101eb192830620cabe2eaa1781](https://github.com/HoTT/HoTT/commit/d79a5b50196a0c101eb192830620cabe2eaa1781).

Compilation:
1. `coq_makefile -f _CoqProject -o Makefile`
2. `make`