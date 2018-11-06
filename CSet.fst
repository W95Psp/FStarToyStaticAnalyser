(**
This module provides finite enumerable sets of arbitrary `a:eqtype`.
Sets are simply lists without duplicates. Equality of two sets means their inner lists have the same elements. 

@summary Finite enumerable non ordered sets
*)
module CSet

open FStar.Tactics
module L = FStar.List.Tot

(** Specify a list without duplicates *)
let rec no_dup (#t:eqtype) (a:list t) = match a with
  | [] -> True
  | h::t -> if L.mem h t then False else no_dup t

(** A set is a list without duplicates *)
let set (a:eqtype) : Type = (r:(list a) { no_dup r })

(** `mem i s` test whether `i` is in `s` *)
let rec mem (#t:eqtype) (x:t) (a:set t) = L.mem x a

// Helper
private let add_in_set' (#t:eqtype) (s:list t { no_dup s }) (x: t) : set t = if L.mem x s then s else x::s
(** `add_in_set s i` is { x | (x in s) or x = i } *)
let add_in_set (#t:eqtype) (x: t) (s:set t) : set t = add_in_set' s x

// Helper
private let union' (#t:eqtype) (a:list t) (b:set t) : set t = L.fold_right add_in_set a b
(** union of two sets *)
let union (#t:eqtype) (a:set t) (b:set t) : set t = union' a b

(** intersection of two sets *)
let rec intersect (#t:eqtype) (a b:set t) : set t = match a with
  | [] -> []
  | h::t -> let l = intersect t b in if mem h b then add_in_set h l else l 

let rec lemma_mem_both_intersect (#t:eqtype) (a b:set t) (x: t)
        : Lemma (mem x a /\ mem x b ==> mem x (intersect a b)) = match a with
  | [] -> ()
  | h::t -> if x = h then ()
		   else lemma_mem_both_intersect t b x
// Converting
let set_to_list (#t:eqtype) (a:set t) : list t = a
let list_to_set (#t:eqtype) (a:list t) : set t = union' a []

let rec findAndRemove (#t:eqtype) (a:set t) (x:t): (bool * set t) = match a with
  | [] -> (false, [])
  | h::t -> if h = x then (true, t) else let (rb,rl) = findAndRemove t h in (rb, add_in_set h rl)

let rec remove (#t:eqtype) (a:set t) (x:t): set t = match a with
  | [] -> []
  | h::t -> if h = x then t else add_in_set h (remove t x)

let rec remove_head (#t:eqtype) (x:t) (a:set t{~(mem x a)}) : Lemma (remove (x::a) x == a) = ()
let rec dup_behead (#t:eqtype) (x:t) (a:list t{no_dup (x::a)}) : Lemma (no_dup a) = ()

let rec stupid_mem (#t:eqtype) (s:list t) (h:t) (x:t{L.mem x (h::s) /\ x <> h}) : Lemma (L.mem x s) = ()

let rec stupid_mem2 (#t:eqtype) (l:set t) (x:t{~(L.mem x l)}) (y:t) : Lemma (~ (L.mem x (remove l y))) = match l with
  | [] -> ()
  | hd::tl -> stupid_mem2 tl x y


let rec remove_lemma (#t:eqtype) (s:set t) (x:t{mem x s}) (h:t{~(mem h s) /\ ~(x = h)})
        : Lemma (h :: (remove s x) == remove (h::s) x) =
        if x = h then ()
        else 
          stupid_mem2 s h x;
          assert (~(L.mem h s));
          assert (~(L.mem h (remove s x)));
          assert (add_in_set h (remove s x) = h::(remove s x))
                
let rec remove_mem_dec (#t:eqtype) (x:t) (a:set t{ mem x a }) : Lemma (L.length (remove a x) = L.length a - 1) = match a with
  | [] -> ()
  | h::t -> if h = x then () else ( remove_mem_dec x t; remove_lemma t x h )

let rec equal (#t:eqtype) (a:set t) (b:set t) : Type0 =
  match a with
  | [] -> b = []
  | h::t -> let (rb, rl) = findAndRemove b h in if rb then equal t rl else false

let rec lemma_union'_no_dup (#t:eqtype) (s:list t{no_dup s}) : Lemma (union' s [] == s) =
  let rec induction (#t:eqtype) (s:list t{no_dup s}) (h:t {~ (mem h s)})
                     : Lemma (union' s [] == s ==> union' (h::s) [] == (h::s)) = match s with
                     | hd::(hd'::tl) -> induction tl hd'
                     | _ -> () in
        match s with
        | [] -> ()
        | hd::tl -> induction tl hd;
                  lemma_union'_no_dup tl

let rec lemma_triv unit : Lemma (true == true <: Prims.Tot Type0) = ()

let rename_get_last name = let l = binders_of_env (cur_env ()) <: list binder in
                           admitP (Cons? l);
                           let b = List.Tot.Base.last l in
                           rename_to b name; b
// match l with
//                          | [] -> fail "Could not find any binders in current env!"
//                          | _  ->  rename_to b name 

let rec lemma_union_step (#t:eqtype) (s:set t) (h:t{~ (mem h s)})
    : Lemma (union' (h::s) [] == h :: (union' s []))
    = admit ()//match s with
    //| hd::(hd'::tl) -> lemma_union_step tl hd'
    //| _ -> ()
    
let rec lemma_convert_wf (#t:eqtype) (s:set t) : Lemma (list_to_set (set_to_list s) `equal` s) =
  let rec induction (#t:eqtype) (s:set t) (h:t{~ (mem h s)}) 
                    : Lemma ((list_to_set (set_to_list s) `equal` s) ==> list_to_set (set_to_list (h::s)) `equal` (h::s))
                    = assert (list_to_set (set_to_list (h::s)) == union' (h::s) []);
                      lemma_union'_no_dup (h :: s);
                      lemma_union_step s h;
                      assert (union' (h::s) [] == h :: (union' s []));
                      () in
          match s with
          | [] -> ()
          | hd::tl -> lemma_convert_wf tl; induction tl hd
                            
                         
  //                        assert_by_tactic (
  //                           (list_to_set (set_to_list s) `equal` s)
  //                        ==> (list_to_set (set_to_list (h::s)) `equal` (h::s))) (fun () -> 
  //                          let ind = implies_intro () in rename_to ind "H";
  //                          unfold_def (`set_to_list);
  //                          unfold_def (`equal);
  //                          unfold_def (`list_to_set);
  //                          squash_intro ();

  //                          focus (fun () ->
                             
  //                            grewrite (quote (union' ())) (quote (h::s))
  //                            //grewrite (quote (union' (h::s) [])) (quote h::s);
  //                            //apply_lemma (`lemma_union'_no_dup)
  //                          );
  //                          //mk_sq_eq (union' (h::s) []) (quote h::s);
  //                          //grewrite (union' (h::s) []) (quote h::s);// (`lemma_union'_no_dup (h::s));
  //                          //let myEq = rename_get_last "myEq" in
  //                          //let hey = unsquash (binder_to_term myEq) in
                        
  //                          //let ploup = lget #(squash (union' (h::s) [] == h :: s)) "uu___" in
  //                          //let equality = unsquash (ploup) in
  //                          //rewrite_eqs_from_context ();
  //                          //compute ();
  //                          //compute ();
  //                          qed ()
  //                        )
  
  
  // assert_by_tactic (list_to_set (set_to_list s) `equal` s) (fun () -> 
  //   unfold_def (`list_to_set);
  //   unfold_def (`union');
  //   destruct (quote (set_to_list s));
  //     // s is nil
  //       unfold_def (`set_to_list);
  //       let snil = intro () in
  //       //apply (`unsquash);
  //       let snil'= unsquash (binder_to_term snil) in
  //       squash_intro ();
  //       rewrite (snil);
  //       compute ();
  //       smt ();
  //    // s is 
  //   qed ()
  // )
 
  // = match s with
  // | [] -> ()
  // | h::t -> assert (list_to_set (set_to_list s)); lemma_convert_wf t

let rec lemma_intersect_empty_l (#t:eqtype) (a:set t) (x:t) : Lemma (mem x (intersect [] a) = false) = ()
let rec lemma_intersect_empty_r (#t:eqtype) (a:set t) (x:t) : Lemma (mem x (intersect a []) = false) = match a with
  | [] -> ()
  | h::t -> lemma_intersect_empty_r t x

let rec lemma_mem_empty (#t:eqtype) (x: t) : Lemma (mem x [] = false) = ()

open FStar.Tactics.PatternMatching

open FStar.Tactics.Logic

let rec lemma_intersect_left (#t:eqtype) (a b:set t) (x: t) : Lemma (mem x (intersect a b) ==> mem x a) = match a with
  | [] -> ()
  | h::t -> if x = h then () else lemma_intersect_left (remove a h) b x


  
let rec lemma_intersect_not_left (#t:eqtype) (a b:set t) (x: t{~(mem x a)}) : Lemma (mem x (intersect a b) == false) = match a with
  | [] -> ()
  | h::t -> lemma_intersect_not_left t b x

let rec lemma_intersect_not_right (#t:eqtype) (a b:set t) (x: t) : Lemma (mem x b == false ==> mem x (intersect a b) == false) =
  let rec helper (#t:eqtype) (a b:set t) (x: t) (ev:mem x b == false) : Lemma (mem x (intersect a b) == false) = match a with
  | [] -> ()
  | h::t -> helper t b x ev in
  assert_by_tactic (mem x b == false ==> mem x (intersect a b) == false) (fun () -> 
    let mem_x_b = implies_intro () in
    apply_lemma (quote (helper a b x));
    apply (binder_to_term mem_x_b);
    //exact_hyp (mem x b == false) mem_x_b;
    qed ()
  )

//let rec lemma_intersect_not_rev (#t:eqtype) (a b:set t) (x:t) : Lemma (mem x (intersect a b))
let rec lemma_intersect_cons_l (#t:eqtype) (a b:set t) (h x: t)
                     : Lemma (no_dup (h::a) ==> ~ (h = x) ==> mem x (intersect (h::a) b) == mem x (intersect a b)) = ()

let rec lemma_intermediaire (#t:eqtype) (a:set t) (h:t) : Lemma (intersect a [h] == [h] \/ intersect a [h] == []) = 
  let rec ind (#t:eqtype) (a:set t) (h:t) (ha:t{no_dup (ha::a)})
    : Lemma (intersect a [h] == [h] \/ intersect a [h] == [] ==> intersect (ha::a) [h] == [h] \/ intersect (ha::a) [h] == []) = () in
    match a with
    | [] -> ()
    | hd::tl -> ind tl h hd; lemma_intermediaire tl h

let rec lemma_intersect_cons_r (#t:eqtype) (a b:set t) (h:t{no_dup (h::b)}) (x: t{~ (h = x)})
                     : Lemma (//no_dup (h::b) ==> ~ (h = x) ==>
                             mem x (intersect a (h::b)) == mem x (intersect a b)) = match b with
    | [] -> lemma_intermediaire a h;
           lemma_intersect_empty_r a x
    | hb::tb -> match a with
      | [] -> ()
      | ha::ta -> if ha = x then (
                   if mem x b then
                     lemma_mem_both_intersect a b x
                   else (
                     lemma_intersect_not_right a b x;
                     lemma_intersect_not_right a (h::b) x;
                     ()
                   )
                ) else (
                  if hb = x then
                    if mem x a then (
                      lemma_mem_both_intersect a (h::b) x;
                      lemma_mem_both_intersect a b x
                    ) else (
                      lemma_intersect_not_left a b x;
                      lemma_intersect_not_left a (h::b) x;
                      ()
                    )
                  else lemma_intersect_cons_r ta b h x
                )

let rec lemma_memIntersect_memRight (#t:eqtype) (a b:set t) (x: t) : Lemma (mem x (intersect a b) ==> mem x b) = match a with
  | [] -> ()
  | h::t -> if h = x then (
                        if (mem h b) then ()
                                     else (lemma_intersect_not_right a b x; assert (mem x (intersect a b) = false); ())
                   ) else lemma_memIntersect_memRight t b x
                   
let rec lemma_memIntersect_memLeft (#t:eqtype) (a b:set t) (x: t) : Lemma (mem x (intersect a b) ==> mem x a) = match a with
        | [] -> ()
        | hd::tl -> if hd = x then ()
                  else lemma_memIntersect_memLeft tl b x

let rec lemma_intersect_mem_both (#t:eqtype) (a b:set t) (x: t) : Lemma (mem x (intersect a b) ==> mem x a /\ mem x b) =
  lemma_memIntersect_memLeft a b x;
  lemma_memIntersect_memRight a b x

let rec lemma_intersect_mem_equiv (#t:eqtype) (a b:set t) (x: t) : Lemma (mem x (intersect a b) <==> mem x a /\ mem x b) =
  lemma_intersect_mem_both a b x;
  lemma_mem_both_intersect a b x


let rec subset (#t:eqtype) (a b:set t) : bool = match a with
  | [] -> true
  | h::t -> if mem h b then subset t (remove b h) else false 



// let rec lemma_subset_implies_mem (#t:eqtype) (a:set t) (b:set t) (x:t{mem x a}) : Lemma (subset a b ==> mem x b) = match a with
//   | [] -> ()
//   | hd::tl -> if hd = x then (
//                ()
//             ) else (
//                lemma_subset_implies_mem tl b x // `subset tl b ==> mem x b`
//             )

let rec lemma_remove' (#t:eqtype) (a:set t) (x:t) (y:t{x <> y}) : Lemma (List.Tot.Base.mem x a ==> mem x (remove a y)) = admit ()
let rec lemma_remove_irrevelant (#t:eqtype) (s:set t) (x:t{~(mem x s)}) : Lemma (remove s x == s) = match s with
  | [] -> ()
  | hd::tl -> lemma_remove_irrevelant tl x

let rec lemma_subset_remove (#t:eqtype) (a b:set t) (h:t{no_dup (h::a)})
  : Lemma (ensures (subset (h::a) b ==> subset a (remove b h)))
          (decreases b) =
  match b with
  | [] -> ()
  | hb::tb -> if mem hb a then (
               remove_lemma a hb h; // rmove (h::a) hb
               assert (remove (h::a) hb == h::(remove a hb));
               assert (no_dup (h::(remove a hb)));
               lemma_subset_remove (remove a hb) tb h
            ) else lemma_subset_remove a tb h

let rec lemma_subset_remove' (#t:eqtype) (a b:set t) (h:t{no_dup (h::a) /\ mem h b})
  : Lemma (subset a (remove b h) ==> subset (h::a) b) = ()

let rec lemma_subset_invert (#t:eqtype) (a:set t) (b:set t) (h:t) (h': t{no_dup (h'::h::a) /\ subset (h'::h::a) b}) : Lemma (subset (h::h'::a) b) = match b with
  | [] -> ()
  | hd::tl -> admit ()

let rec lemma_subset_add (#t:eqtype) (a:set t) (b:set t{subset a b}) (h:t{no_dup (h::a) /\ mem h b}) : Lemma (subset (h::a) b) =
  match a with
  | [] -> ()
  | ha::ta -> if mem ha b then (
     assert (no_dup (ha::ta));
     assert (mem ha b);
     assert (no_dup (h::ta));

     assert (subset a b = subset ta (remove b ha));

     lemma_subset_remove ta b ha;
     assert (subset ta (remove b ha));

     
     assert (no_dup (h::ta));
     assert (mem h b);
     lemma_remove' b h ha;
     assert (mem h (remove b ha));
     lemma_subset_add ta (remove b ha) h;
     
     assert (subset ta (remove b ha) ==> subset (h::ta) (remove b ha));

     lemma_subset_remove' (h::ta) b ha;
     assert (subset (h::ta) (remove b ha) ==> subset (ha::h::ta) b);
     lemma_subset_invert ta b h ha
   ) else (
     assert (subset a b = false);
     ()
   )

// let rec lemma_still_subset_behead (#t:eqtype) (a:set t) (b:set t) (h:t{no_dup (h::a)}) : Lemma (subset (h::a) b ==> subset a b) =
//    lemma_subset_add a b h
  
// let rec lemma_still_subset_add (#t:eqtype) (a: set t) (b:set t{subset a b}) (h: t{~(mem h b)}) : Lemma (subset a (h::b)) = match a with
//   | [] -> ()
//   | hd::tl -> lemma_still_subset_add tl b h  

// let rec lemma_subset_forall (#t:eqtype) (a:set t) (b:set t{subset a b}) (x: t) : Lemma (mem x a ==> mem x b) = match a with
//   | [] -> ()
//   | hd::tl -> if hd = x then
//                if mem hd b then ()
//                else (
//                  lemma_subset_forall a (remove b hd) x
//                )
//             else admit ()// lemma_subset_forall hd b x

// let rec lemma_subset (#t:eqtype) (a b:set t) : Lemma (subset (intersect a b) a) = match intersect a b with
//   | [] -> ()
//   | h::t -> 
//         assert (mem h (intersect a b));
//         lemma_memIntersect_memRight (intersect a b) a h;
//         assert (mem h a);
//         lemma_subset (remove a h) (remove b h)

//let rec lemma_subset (#t:eqtype) (a:set t) (b:set t) 
let rec lemma_no_dup_remove (#t:eqtype) (l:list t{no_dup l}) (x:t) : Lemma (no_dup (remove l x)) = ()

let rec lemma_subset_trans (#t:eqtype) (a:set t) (b:set t{subset a b}) (c:set t{subset b c}) : Lemma (subset a c) = admit ()
let rec lemma_subset_ref (#t:eqtype) (a: set t) : Lemma (subset a a) = admit ()
let rec lemma_subset_sym (#t:eqtype) (a b:set t) : Lemma (subset a b /\ subset b a ==> a `equal` b) = admit ()


let rec singleton (#t:eqtype) (a:t) : set t = [a]
