(*
 * Copyright (c) 2021-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.lib.fractional.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.iris.extra.bi.errors.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.iris.extra.bi.spec.frac_splittable.
Require Import bluerock.iris.extra.bi.spec.nary_classes.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.destroy.
Require Import bluerock.lang.cpp.logic.initializers.
Require Import bluerock.lang.cpp.logic.dispatch.
Require Import bluerock.lang.cpp.logic.wp.
Require Import bluerock.lang.cpp.logic.call.
Require Import bluerock.lang.cpp.logic.translation_unit.

Module Type Expr__newdelete.

  #[local] Open Scope free_scope.
  (* hide [genv] argument, it's a typeclass anyway *)
  #[local] Arguments size_of {_} _ : assert.

  (**
   * Weakest pre-condition for [new] and [delete] expressions
   *
   * The semantics of <<new>> and <<delete>> expressions (including their array forms)
   * are *very* complex in C++. This is due to a litany of corner cases such as:
   * - the need to pair allocation and de-allocation functions
   * - the existance of placement <<new>>
   * - the need to handle alignment as well as size.
   * - the potential for padding bytes.
   * - the potential to merge allocations. (BRiCk does not attempt to support this)
   *
   * NOTE It is important that these rules are sound, but less important that
   * they are complete. When in doubt, we err on the side of caution and under-specify
   * the behavior of various constructs.
   *
   * If you run into code that requires addditional semantic specification, please file
   * an issue.
   *)

  (** Dynamic Typing at <<delete>>-Time

      The C++ Standard ascribes undefined behavior to any <<delete>>-calls which
      have a Static Type which differs from the Dynamic Type that was associated
      with the pointer when it was initially created via <<new>>
      <https://eel.is/c++draft/expr.delete#3>:
      | (3) In a single-object delete expression, if the static type of the object to be
      |     deleted is not similar ([conv.qual]) to its dynamic type and the selected
      |     deallocation function (see below) is not a destroying operator delete, the
      |     static type shall be a base class of the dynamic type of the object to be
      |     deleted and the static type shall have a virtual destructor or the behavior is
      |     undefined. In an array delete expression, if the dynamic type of the object to
      |     be deleted is not similar to its static type, the behavior is undefined.
      [new_token.R q allocation_type] tracks this Dynamic Type information.

      Making this [Fractional] instead of [Exclusive] helps write representation
      predicates for classes like the following:
      <<
      class Foo {
        int* x;
        Foo() : x(new int) {}
      };
      >>

      [obj |-> new_token.R q (new_token.mk ty storage ptr offset)] is ownership that:
      - [obj] is the constructed object pointer
      - [ty] is the <<new>>d type, *including qualifiers*.
      - [storage_ptr] is the block storage pointer that underlies [obj],
        see [new_token_provides_storage].
      - [offset] is the size of the meta-data owned by the C++ abstract machine.
        This overhead lives at [storage_ptr .[ Tbyte ! -offset) |-> blockR 1 offset].
   *)

  #[global] Notation Tbyte := Tuchar (only parsing).

  Module new_token.
    Record t := mk
      { alloc_ty : type
      ; storage_ptr : ptr
      ; overhead : N
      }.

    Definition mkBase  `{σ : genv} ty storage_base (overhead : N)
      := mk ty (storage_base .[ Tbyte ! overhead ]) overhead.

    #[global] Notation storage_base d
      := (d.(storage_ptr) .[ Tuchar ! - d.(overhead) ]).

    Parameter R : forall `{Σ : cpp_logic} {σ : genv} (q : Qp) (data : t), Rep.
    #[global] Arguments R {_ _ _ σ} _%_Qp _%_N.

    Section with_cpp_logic.
      Context `{Σ : cpp_logic} {σ : genv}.

      #[global] Declare Instance Observe_provides_storage : forall obj q d,
          Observe (provides_storage d.(storage_ptr) obj d.(alloc_ty))
            (obj |-> R q d).

      #[global] Declare Instance Observe_type_size : forall q d,
          Observe [| exists sz, size_of d.(alloc_ty) = Some sz |]
            (R q d).

      #[global] Declare Instance R_frac :
        FracSplittable_1 R.
      #[global] Declare Instance R_agree :
        AgreeF1 R.

    End with_cpp_logic.
  End new_token.

  Section with_cpp_logic.
    Context `{Σ : cpp_logic} {σ : genv}.

    Section with_region.

      Context (ρ : region).
      Variable (tu : translation_unit).

      #[local] Notation wp_init := (wp_init tu ρ).
      #[local] Notation wp_initialize := (wp_initialize tu ρ).
      #[local] Notation default_initialize := (default_initialize tu).
      #[local] Notation wp_operand := (wp_operand tu ρ).
      #[local] Notation wp_args := (wp_args tu ρ).

      (* <<std::align_val_t>> *)
      #[local] Notation Talign_val_t := (Tenum $ Nscoped (Nglobal $ Nid "std") (Nid "align_val_t")) (only parsing).
      #[local] Notation Tbyte := Tuchar (only parsing).

      Section new.
        (** [new (...) C(...)] <https://eel.is/c++draft/expr.new>
            - invokes a C++ new operator [new_fn], which returns a storage pointer [storage_ptr];
              [new_fn] _might_ allocate memory
              (<https://eel.is/c++draft/expr.new#10>), or return an argument
              address for some forms of placement new;
            - constructs an object pointer [obj_ptr], which shares the address of [storage_ptr];
            - invokes the constructor C over [obj_ptr].

            Furthermore <https://eel.is/c++draft/expr.new#22>:
            | (22) A new-expression that creates an object of type <<T>> initializes that
            |      object as follows:
            | (22.1) If the new-initializer is omitted, the object is default-initialized
            |        ([dcl.init]).
            |        [Note 12: If no initialization is performed, the object has an
            |         indeterminate value. — end note]
            | (22.2) Otherwise, the new-initializer is interpreted according to the
            |        initialization rules of [dcl.init] for direct-initialization.
            We use [default_initialize] for default ininitialization as it is defined in the
            C++ Standard and we use [wp_init] for direct-initialization as defined
            by the C++ Standard.

            ~~~ Implementation Details ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

            - This axiom assumes that [storage_ptr] points to a character array that will
              _provide storage_ for a new _complete object_ [o]
              (<http://eel.is/c++draft/intro.object#def:provides_storage>).

              In that case, the C++ abstract machine can choose to make [obj_ptr
              <> storage_ptr] (while keeping the same address), so that the old
              pointer [storage_ptr] cannot be used to access the new object.
              Inspired by Cerberus, we model this by _allowing_ [obj_ptr] to have
              a different allocation ID.

            - The created object might be a subobject of an existing object
              (pointed to by some pointer [p])
              (<https://eel.is/c++draft/basic.memobj#intro.object-2>).
              It is unclear whether that requires [storage_ptr = p] or just
              [provides_storage storage_ptr p].
              In that case, we plan to allow proving that [obj_ptr] = [p ., o]; we
              offer no such support at present; we account for this case by not specifying that
              [ptr_alloc_id obj_ptr <> ptr_alloc_id storage_ptr].
            - Currently, we do not model coalescing of multiple allocations
              (<https://eel.is/c++draft/expr.new#14>).
         *)
        Definition wp_opt_initialize (oinit : option Expr) aty obj_ptr :=
          match oinit with
          | None => (* default_initialize the memory *)
            default_initialize aty obj_ptr
          | Some init => (* Use [init] to initialize the memory *)
            wp_initialize aty obj_ptr init
          end.
        #[global] Arguments wp_opt_initialize !_ _ _ /.

        (* This function takes the size and alignment explicitly because
           the semantics of <<operator new[]>> can add an unspecified amount
           of overhead to the allocation.

           Question: Is it possible for the C++ abstract machine to pass an
           alignment that is different than the alignment of the object type?
         *)
        Definition new_implicits (pass_align : bool) (sz al : N) : list Expr :=
          (* the evaluation of these expressions implicitly check that the
             values are representable in their respective types *)
          [Eint sz Tsize_t] ++
            if pass_align
            then [Ecast (Cintegral Talign_val_t) (Eint al Tsize_t)]
            else [].

        Axiom wp_operand_new :
          forall (oinit : option Expr)
            new_fn (pass_align : bool) new_args aty Q targs
            (nfty := normalize_type new_fn.2)
            (_ : (args_for <$> as_function nfty) = Some targs)
            (alloc_sz alloc_al : N)
            (_ : size_of aty = Some alloc_sz) (_ : align_of aty = Some alloc_al),
            (let implicit_args := new_implicits pass_align alloc_sz alloc_al in
             letI* _, vs, ifree, free :=
               wp_args evaluation_order.nd [] targs (implicit_args ++ new_args) in
             |> letI* res := wp_fptr tu.(types) nfty (_global new_fn.1) vs in
                letI* := interp tu ifree in
                letI* storage_val := operand_receive (Tptr Tvoid) res in
                Exists storage_ptr : ptr,
                  [| storage_val = Vptr storage_ptr |] **
                  if bool_decide (storage_ptr = nullptr) then
                    [| new_args <> nil |] ** Q (Vptr storage_ptr) free
                    (* ^^ [new_args <> nil] exists because the default <<operator new>>
                       is never allowed to return [nullptr] *)
                  else
                    (* C++ requires the resulting pointer to be aligned to
                        <<__STDCPP_DEFAULT_NEW_ALIGNMENT__>> even in cases when the
                        required alignment is actually smaller. When the alignment is
                        smaller, [pass_align] will be [false]. *)
                    storage_ptr |-> alignedR (if pass_align then alloc_al
                                              else STDCPP_DEFAULT_NEW_ALIGNMENT) **
                    storage_ptr |-> blockR alloc_sz 1$m **
                    (Forall (obj_ptr : ptr),
                       provides_storage storage_ptr obj_ptr aty -*
                       letI* free' := wp_opt_initialize oinit aty obj_ptr in
                        (* This also ensures these pointers share their
                          address (see [provides_storage_same_address]) *)
                        (* Track the type we are allocating
                          so it can be checked at [delete].
                          It is important that this preserves
                          `const`ness of the type.
                        *)
                        obj_ptr |-> new_token.R 1 (new_token.mk aty storage_ptr 0) -*
                        Q (Vptr obj_ptr) (free' >*> free)))
        |-- wp_operand (Enew new_fn new_args (new_form.Allocating pass_align) aty None oinit) Q.

        (** The C++ standard distinguishes placement/non-allocating forms in
         *  <https://eel.is/c++draft/new.delete.placement#1>.
         *
         *  NOTE: placement <new> is more subtle than the rule described here
         *  because it can be used to construct an object over an existing
         *  object.
         *)
        Axiom wp_operand_non_allocating_new :
          forall (oinit : option Expr)
            new_fn storage_expr aty Q
            (nfty := normalize_type new_fn.2)
            (_ : args_for <$> as_function nfty = Some ([Tsize_t; Tptr Tvoid], Ar_Definite)),
            (Exists alloc_sz alloc_al,
               [| size_of aty = Some alloc_sz |] **
               [| align_of aty = Some alloc_al |] ** (** <-- TODO FM-975 *)
             letI* _, vs, ifree, free :=
               wp_args evaluation_order.nd [] ([Tsize_t;Tptr Tvoid], Ar_Definite)
                 [Eint alloc_sz Tsize_t; storage_expr] in
             Exists storage_ptr,
               (Exists size_loc storage_loc,
                 [| vs = [size_loc; storage_loc] |] **
                 storage_loc |-> primR (Tptr Tvoid) 1$m (Vptr storage_ptr) ** True) //\\
               (|> letI* res := wp_fptr tu.(types) nfty (_global new_fn.1) vs in
                 letI* := interp tu ifree in
                 res |-> primR (Tptr Tvoid) 1$m (Vptr storage_ptr) **
                 (* ^^ this line requires the function to return the passed pointer.
                    This is mandated by the standard, see, e.g.
                    <https://eel.is/c++draft/new.delete.placement#2>
                  *)
                  [| storage_ptr <> nullptr |] **
                  (* ^^ mostly redundant with next line except for 0-sized objects *)
                  storage_ptr |-> blockR alloc_sz 1$m **
                  storage_ptr |-> alignedR alloc_al **
                  (Forall (obj_ptr : ptr),
                      (* This also ensures these pointers share their
                        address (see [provides_storage_same_address]) *)
                      provides_storage storage_ptr obj_ptr aty -*
                      letI* free' := wp_opt_initialize oinit aty obj_ptr in
                        (* Track the type we are allocating
                          so it can be checked at [delete].
                          It is important that this preserves
                          `const`ness of the type.
                        *)
                        obj_ptr |-> new_token.R 1 (new_token.mk aty storage_ptr 0) -*
                        Q (Vptr obj_ptr) (free' >*> free))))
        |-- wp_operand (Enew new_fn [storage_expr] new_form.NonAllocating aty None oinit) Q.

        (* A size such that if the requested allocation size is less than this, the C++
           abstract machine is guaranteed to be able to find a suitable overhead such
           that there is an allocation that can satisfy the requirements. See
           <https://eel.is/c++draft/implimits#2.17>

           The C++ standard recommends that this value be greater than <<262,144>>.
         *)
        Parameter SIZE_MAX : N.

        Axiom wp_operand_array_new :
          forall (array_size : Expr) (oinit : option Expr)
            new_fn (pass_align : bool) new_args aty Q targs
            (nfty := normalize_type new_fn.2)
            (_ : args_for <$> as_function nfty = Some targs),
            (* <https://eel.is/c++draft/expr.new#7>
               | (7) Every constant-expression in a noptr-new-declarator shall be a
               |     converted constant expression ([expr.const]) of type std​::​size_t
               |     and its value shall be greater than zero.
               |     [Example 4: Given the definition int n = 42, new float[n][5] is
               |      well-formed (because n is the expression of a noptr-new-declarator),
               |      but new float[5][n] is ill-formed (because n is not a constant
               |      expression). — end example]
               If we're allocating a new array, we know that the expression must reduce
               to a constant value of type [size_t] /and/ that it must be sequenced
               before we call the [new_fn].
             *)
            (letI* v, free := wp_operand array_size in
              (* Valid C++ programs require this value to be a [Vint] (see the quote from
                 <expr.new#7> above). *)
              Exists array_sizeN, [| v = Vn array_sizeN |] **
                (* The size must be non-negative. *)
                [| 0 <= array_sizeN |]%N **
                Exists alloc_sz alloc_al,
                let array_ty := Tarray aty array_sizeN in
                [| size_of array_ty = Some alloc_sz |] **
                [| align_of aty = Some alloc_al |] ** (** <-- TODO FM-975 *)
                (* NOTE: This is [Forall overhead_sz] because the C++ Abstract Machine can choose
                          however many bytes it wants to use for metadata when handling
                          dynamically allocated arrays; however, it can not be *completely*
                          unconstrained because the allocated size plus the overhead
                          must fit within <<size_t>>. If it does not, [nullptr] is returned
                          (or <<std::bad_array_new_length>> is thrown, but BRiCk does not
                          support exceptions).
                          See <https://eel.is/c++draft/expr.new#8.6>.
                  *)
                [| has_type_prop alloc_sz Tsize_t |] **
                (([| (SIZE_MAX < alloc_sz)%N |] -* Q (Vptr nullptr) free) //\\
                 (* ^^ handles when the overhead exceeds the size *)
                Forall overhead_sz : N,
                  [| has_type_prop (overhead_sz + alloc_sz)%N Tsize_t |] -*
                  let implicit_args :=
                      new_implicits pass_align (overhead_sz + alloc_sz) alloc_al in
                  letI* _, vs, ifree, free' :=
                      wp_args evaluation_order.nd [] targs (implicit_args ++ new_args) in
                  |> letI* res := wp_fptr tu.(types) nfty (_global new_fn.1) vs in
                     letI* := interp tu ifree in
                     Exists (storage_base : ptr),
                     res |-> primR (Tptr Tvoid) 1$m (Vptr storage_base) **
                     if bool_decide (storage_base = nullptr) then
                       [| new_args <> nil |] ** Q (Vptr storage_base) free
                       (* ^^ [new_args <> nil] exists because the default <<operator new>>
                          is never allowed to return [nullptr] *)
                     else
                       (* [blockR alloc_sz -|- tblockR (Tarray aty array_size)] *)
                      storage_base |-> blockR (overhead_sz + alloc_sz) 1$m **
                      storage_base |-> alignedR (if pass_align then alloc_al else STDCPP_DEFAULT_NEW_ALIGNMENT) **
                      (Forall (obj_ptr : ptr),
                        storage_base .[Tbyte ! overhead_sz] |-> alignedR alloc_al -*
                        (* This also ensures these pointers share their
                        address (see [provides_storage_same_address]) *)
                        provides_storage
                          (storage_base .[Tbyte ! overhead_sz])
                          obj_ptr array_ty -*
                        letI* free'' := wp_opt_initialize oinit array_ty obj_ptr in
                          (* Track the type we are allocating
                            so it can be checked at [delete]
                            *)
                          obj_ptr |-> new_token.R 1 (new_token.mkBase array_ty storage_base overhead_sz) -*
                          Q (Vptr obj_ptr) (free'' >*> free' >*> free))))
        |-- wp_operand (Enew new_fn new_args (new_form.Allocating pass_align) aty (Some array_size) oinit) Q.

        (* We deliberately avoid giving a reasoning principle for array-placement <<new>> since
           it is generally not used and compilers differ in the semantics.
         *)

      End new.
    End with_region.

    (** *** [wp_delete] *)
    Definition alloc_pointer (pv : ptr) (Q : ptr -> FreeTemp -> mpred) : mpred :=
      Forall p : ptr, p |-> primR (Tptr Tvoid) 1$m (Vptr pv) -* Q p (FreeTemps.delete (Tptr Tvoid) p).

    Lemma alloc_pointer_frame : forall p Q Q',
        Forall p fr, Q p fr -* Q' p fr |-- alloc_pointer p Q -* alloc_pointer p Q'.
    Proof.
      intros; rewrite /alloc_pointer. iIntros "X Y".
      iIntros (?) "p"; iApply "X"; iApply "Y"; done.
    Qed.

    (** [resolve_dtor ty obj_ptr' Q] resolves the destructor for the object [obj_ptr'] (of type [ty]).
        The continuation [Q] is passed the pointer to the most-derived-object of [obj_ptr] and its type.
      *)
    Definition resolve_dtor (tu : translation_unit) (ty : type) (obj_ptr' : ptr) (Q : ptr -> type -> mpred) : mpred :=
      match drop_qualifiers ty with
      | Tqualified _ ty => False (* unreachable *)
      | Tnamed cls      =>
        match tu.(types) !! cls with
        | Some (Gstruct s) =>
          if has_virtual_dtor s then
            (* NOTE [has_virtual_dtor] could be derived from the vtable... *)
            (* In this case, use virtual dispatch to invoke the destructor. *)
            letI* fimpl, impl_class, obj_ptr := resolve_virtual obj_ptr' cls s.(s_dtor) in
            let r_ty := Tnamed impl_class in
            Q obj_ptr r_ty
          else
            Q obj_ptr' (erase_qualifiers ty)
        | Some (Gunion u)  =>
          (* Unions cannot have [virtual] destructors: we directly invoke the destructor. *)
          Q obj_ptr' (erase_qualifiers ty)
        | _                => False
        end
      | Tarray _ _
      | Tincomplete_array _
      | Tvariable_array _ _ =>
        Q obj_ptr' (erase_qualifiers ty)
      | Tref r_ty
      | Trv_ref r_ty    =>
        False (* references can not be deleted, only destroyed *)
      | ty              =>
        Q obj_ptr' (erase_qualifiers ty)
      end%I.

    Lemma resolve_dtor_frame : forall tu ty p Q Q',
        Forall p t, Q p t -* Q' p t |-- resolve_dtor tu ty p Q -* resolve_dtor tu ty p Q'.
    Proof.
      rewrite /resolve_dtor; intros.
      iIntros "X"; repeat case_match; eauto; try solve [ iApply wp_fptr_frame; iIntros (?); eauto ].
      iApply resolve_virtual_frame. iIntros (???); iApply "X".
    Qed.

    Definition cv_compat (t1 t2 : type) : Prop :=
      erase_qualifiers t1 = erase_qualifiers t2.

    Lemma cv_compat_refl ty :
      cv_compat ty ty.
    Proof. done. Qed.

  End with_cpp_logic.

  Definition array_compatible (is_array : bool) (ty : type) : Prop :=
    match ty with
    | Tarray _ _ => is_array = true
    | Tincomplete_array _
    | Tvariable_array _ _ => False
    | _ => is_array = false
    end.

    (* [delete_val default ty p Q] is the weakest pre-condition of deleting [p] (of type [ty]).
        In the case that [ty] has a custom [operator delete], that function will be called, otherwise
        the [default] delete operator will be used.

        TODO: This does *not* support destroying <<delete>> introduced in C++20.
      *)
    mlock
    Definition delete_val `{Σ : cpp_logic} {σ : genv} tu (default : obj_name * type) (ty : type) (p : ptr) (Q : mpred) : mpred :=
      let del_type := Tfunction $ FunctionType Tvoid (Tptr Tvoid :: nil) in
      let del '(fn, ty) :=
          (letI* p', free := alloc_pointer p in
          |> letI* p := wp_fptr tu.(types) ty (_global fn) (p' :: nil) in
              letI* := interp tu free in
              letI* _ := operand_receive Tvoid p in Q)%I
      in
      match erase_qualifiers ty with
      | Tnamed nm =>
        match tu.(types) !! nm with
        | Some (Gstruct s) =>
          del $ from_option (fun x => (x, del_type)) default s.(s_delete)
        | Some (Gunion u) =>
          del $ from_option (fun x => (x, del_type)) default u.(u_delete)
        | _ => False
        end
      | _ => del default
      end.

    Lemma delete_val_frame `{Σ : cpp_logic} {σ : genv} : forall tu default ty p Q Q',
        Q -* Q' |-- delete_val tu default ty p Q -* delete_val tu default ty p Q'.
    Proof.
      rewrite delete_val.unlock; intros.
      iIntros "X"; repeat case_match; eauto; iApply alloc_pointer_frame; iIntros (??);
      iIntros "Y !>"; iRevert "Y";
      iApply wp_fptr_frame; iIntros (?); iApply interp_frame; iApply operand_receive_frame; iIntros (?); done.
    Qed.

  (* [wp_delete] encapsulates the logic needed to <<delete>> an
      object of a particular type.

      In the future, when we support C++20's destroying <<delete>>, we
      can insert the appropriate logic here to select the right way
      to destroy the object.
    *)
  mlock
  Definition wp_delete `{Σ : cpp_logic} {σ : genv} (tu : translation_unit) (delete_fn : _) (array : bool) destroyed_type obj_ptr Q : mpred :=
    denoteModule tu -*
    letI* this', mdc_ty := resolve_dtor tu destroyed_type obj_ptr in
    Exists cv_mdc storage_ptr overhead,
      this' |-> new_token.R 1 (new_token.mk cv_mdc storage_ptr overhead) ** [| cv_compat cv_mdc mdc_ty |] **
      [| array_compatible array cv_mdc |] **
      Exists tu', denoteModule tu' **
      letI* := destroy_val tu' cv_mdc this' (* << invoke the destructor *) in
        Exists (sz : N), [| size_of mdc_ty = Some sz |] **
          (storage_ptr .[ Tuchar ! -overhead ] |-> blockR (overhead + sz) 1$m
            -* delete_val tu' delete_fn mdc_ty (storage_ptr .[ Tuchar ! -overhead ]) (Q Vvoid)).

  Section delete.
    Context `{Σ : cpp_logic} {σ : genv}.

    Section with_region.
      Variable (tu : translation_unit).
      Context (ρ : region).
      #[local] Notation wp_operand := (wp_operand tu ρ).

      Lemma wp_delete_frame : forall tu fn ary ty p Q Q',
          Forall p, Q p -* Q' p |-- wp_delete tu fn ty ary p Q -* wp_delete tu fn ty ary p Q'.
      Proof.
        rewrite wp_delete.unlock; intros.
        iIntros "X Y M"; iSpecialize ("Y" with "M"); iRevert "Y".
        iApply resolve_dtor_frame; iIntros (??) "Y".
        iDestruct "Y" as (???) "Y".
        iExists _, _, _.
        iDestruct "Y" as "[$[$[$Y]]]".
        iDestruct "Y" as (?) "Y".
        iExists _; iDestruct "Y" as "[$ Y]".
        iRevert "Y"; iApply destroy_val_frame; first reflexivity.
        iIntros "Y"; iDestruct "Y" as (?) "Y"; iExists _; iDestruct "Y" as "[$ Y]".
        iIntros "Z"; iSpecialize ("Y" with "Z").
        iRevert "Y"; iApply delete_val_frame. eauto.
      Qed.

      (* <<delete>>

          https://eel.is/c++draft/expr.delete

          NOTE: https://eel.is/c++draft/expr.delete#7.1 says:
          > The value returned from the allocation call of the new-expression
          > shall be passed as the first argument to the deallocation function.

          Hence, the destructor is passed a pointer to the object, and the
          deallocation function <<delete>> is passed a pointer to the
          underlying storage (of type <<void *>>).

          On deleting null:
          From the C++ standard (<https://en.cppreference.com/w/cpp/language/delete>)

          > If expression evaluates to a null pointer value, no destructors are
          > called, and the deallocation function may or may not be called (it's
          > unspecified), but the default deallocation functions are guaranteed
          > to do nothing when passed a null pointer.

          NOTE: [Edelete]'s first argument is [true] iff the expression corresponds to
          an array-delete, i.e. <<delete[]>>.
        *)
      Axiom wp_operand_delete :
        forall delete_fn e destroyed_type Q
          (dfty := normalize_type delete_fn.2)
          (_ : args_for <$> as_function dfty = Some ([Tptr Tvoid], Ar_Definite)),
        (* call the destructor on the object, and then call delete_fn *)
        (letI* v , free := wp_operand e in
          Exists obj_ptr, [| v = Vptr obj_ptr |] **
          if bool_decide (obj_ptr = nullptr)
          then
            (* this conjunction justifies the compiler calling the delete function
                or not calling it when the argument is null. *)
              (delete_val tu delete_fn destroyed_type obj_ptr $ Q Vvoid free)
            ∧ Q Vvoid free
          else
            (* v---- Calling destructor with object pointer *)
            wp_delete tu delete_fn false destroyed_type obj_ptr (fun v => Q v free))
      |-- wp_operand (Edelete false delete_fn e destroyed_type) Q.

      (** [wp_operand_delete_default] specializes [wp_operand_delete] for invocations of
        *  the form <<delete p;>> - where <<p>> is a non-null pointer to an object whose
        *  most-derived destructor is defined in the current translation unit.
        *)
      Lemma wp_operand_delete_default :
        forall delete_fn e destroyed_type Q
          (dfty := normalize_type delete_fn.2)
          (_ : args_for <$> as_function dfty = Some ([Tptr Tvoid], Ar_Definite)),
        (* call the destructor on the object, and then call delete_fn *)
        (letI* v, free := wp_operand e in
            Exists obj_ptr, [| v = Vptr obj_ptr |] ** [| obj_ptr <> nullptr |] **
            (* v---- Calling destructor with object pointer *)
              wp_delete tu delete_fn false destroyed_type obj_ptr (fun v => Q v free))
      |-- wp_operand (Edelete false delete_fn e destroyed_type) Q.
      Proof.
        intros **; iIntros "operand".
        iApply wp_operand_models; iIntros "#MOD".
        iApply wp_operand_delete; eauto; cbn.
        iApply (wp_operand_frame _ tu); [by reflexivity | | by iFrame].
        iIntros (v free) "H"; iDestruct "H" as (obj_ptr) "(-> & % & dtor_lookup)".
        iExists obj_ptr; iSplitR; first done.
        rewrite bool_decide_false; last assumption.
        iApply wp_delete_frame; eauto.
      Qed.

      (* NOTE: [destroyed_type] will refer to the /element/ of the array *)
      Axiom wp_operand_array_delete :
        forall delete_fn e destroyed_type Q
          (dfty := normalize_type delete_fn.2)
          (_ : args_for <$> as_function dfty = Some ([Tptr Tvoid], Ar_Definite)),
        (* call the destructor on the object, and then call delete_fn *)
        (letI* v, free := wp_operand e in
          Exists obj_ptr, [| v = Vptr obj_ptr |] **
          Exists array_size,
          let array_ty := Tarray destroyed_type array_size in
          if bool_decide (obj_ptr = nullptr)
          then
            (* this conjunction justifies the compiler calling the delete function
              or not calling it. *)
              delete_val tu delete_fn array_ty nullptr (Q Vvoid free)
            ∧ Q Vvoid free
          else (
            (* TODO: the only downside that I see to using [wp_delete] here instead
              of inlining it is that the AST has already fixed the deallocation function *)
            wp_delete tu delete_fn true array_ty obj_ptr (fun v => Q v free)))
      |-- wp_operand (Edelete true delete_fn e destroyed_type) Q.

      Section NOTE_potentially_relaxing_array_delete.
        (* While (we currently think) it is UB to delete [auto p = new int[5][6]]
            using [delete[] &(p[0][0])], it seems like clang still does something
            sensible for this. If we want to relax our axioms in the future to
            allow for this sort of behavior, we could relate the "carrier type"
            and the "dynamic type" of the array which was allocated (which is stored
            in the [new_token]).

            In particular, so long as the [obj_ptr] [p'] we delete is syntactically
            identical to the [obj_ptr] [p] returned by our array-new call /and/
            the "carrier type" of the delete is _similar_
            <https://eel.is/c++draft/conv.qual> to the "carrier type" of
            the array, we can use [p'] to delete the object rooted at [p].

            NOTE: we might need to insert [erase_qualifiers]/[normalize_type] calls to
            reflect that the standard only calls for "similarity"
            (which has a more nuanced consideration of cv-qualifiers).
          *)

        (* If we have [Tarray ty sz], [array_carrier_type ty] strips all of the outermost
            [Tarray]s off and returns the "carrier type" of the array.
          *)
        Fixpoint array_carrier_type (ty : type) : type :=
          match ty with
          | Tarray ty' _ => array_carrier_type ty'
          | _ => ty
          end.
      End NOTE_potentially_relaxing_array_delete.
    End with_region.
  End delete.
End Expr__newdelete.

Declare Module E__newdelete : Expr__newdelete.

Export E__newdelete.
