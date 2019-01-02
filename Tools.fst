module Tools

let (@@) #a #b #c (f: b -> c) (g: a -> b) (v:a) = f (g v) 

let ( |> ) (v:'a) (f: 'a -> 'b): 'b = f v
let ( <| ) (f: 'a -> 'b) (v:'a): 'b = f v

