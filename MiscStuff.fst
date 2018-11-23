module MiscStuff
// type interval = i:interval'{match i with
//   | EmptyInterval -> True
//   | SomeInterval a b -> a `lt` b}

let ( @ ) #a #b #c (g:b->c) (f:a->b) (v:a) = g (f v)
let dup #a #b #z (f : a -> a -> b) (t : z -> a) (v:z) (w:z) = (f (t v) (t w))

// class intervalHelper a = {
//   mkInterval : a -> interval
// }

let uncurryP #t1 #t2 #t3 p (f:(t:(tuple2 t1 t2){p (fst t) (snd t)})->t3)
	     (a:t1) (b:t2{p a b}) = f (a, b)

let curryP #t1 #t2 #t3 p (f:(x:t1)->(y:t2{p x y})->t3)
	      (t:(tuple2 t1 t2){p (fst t) (snd t)}) : t3
  = let (a,b) = t in f a b

// let ltL a b = (a `lt` b) == true
