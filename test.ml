let __op    9   .
            8   ++
            7   @@
           -1   <<
            1   >>
let . f g x = f (g x)
let << f x = f x
let >> x f = f x
let id x = x
let const k x = x
let not x = if x then false else true
let even? x = x rem 2 == 0
let odd? x = x rem 2 == 1
let negative? x = x < 0
let zero? x = x == 0
let positive? x = x > 0
let succ x = 1 + x
let pred x = -1 + x
let flip f x y = f y x
let pair x y = (x, y)
let fst pair = let (x, _) = pair in x
let snd pair = let (_, x) = pair in x
let curry f x y = f (x, y)
let uncurry f xy = f (fst xy) (snd xy)
let hd xs = if xs | x:_ -> x
let tl xs = if xs | _:xs -> xs
let __op 1 ⊕ in
let rec foldr ⊕ seed xs =
    if xs
    | [] -> seed
    | x:xs -> x ⊕ (foldr (⊕) seed xs)
let rec foldr1 ⊕ xs =
    if xs
    | x:y:[] -> x ⊕ y
    | x:xs -> x ⊕ (foldr1 (⊕) xs)
let rec foldl ⊕ seed xs =
    if xs
    | [] -> seed
    | x:xs -> foldl (⊕) (seed ⊕ x) xs
let rec foldl1 ⊕ xs = foldl (⊕) (hd xs) (tl xs)
let ++ xs ys = foldr (:) ys xs
let reverse xs = foldl (flip (:)) [] xs
let copy xs = foldr (:) [] xs
let map f xs = foldr (fun x rest -> f x : rest) [] xs
let filter ok? xs = let f x rest =  if ok? x
                                    then x : rest
                                    else rest
                    in foldr f [] xs
let concat xss = foldr (++) [] xss
let length xs = foldl (fun n _ -> 1 + n) 0 xs
let all? ok? xs = foldl (fun rest x -> rest and ok? x) true xs
let rec any? ok? xs =
    if xs
    | [] -> false
    | x:xs -> ok? x or any? ok? xs
let elem x xs = any? (== x) xs
let sum xs = foldl (+) 0 xs
let product xs = foldl (*) 1 xs
let min x y = if x < y then x else y
let max x y = if x > y then x else y
let minimum xs = foldl1 min xs
let maximum xs = foldl1 max xs
let between a c b = a <= b and b <= c
let splitat index xs =
    let rec repeat index state =
        let (output, remaining) = state in
            if index == 0
            then (reverse output, remaining)
            else let (first : remaining) = remaining
                 in repeat (index - 1) (first : output, remaining)
    in repeat index ([], xs)
let echo x = let _ = print x
             let _ = print "\n"
             in x
let @@ str i =  if i >= 0
                then subs i (i + 1) str
                else let n = lengths str
                     in subs (i + n) (i + n + 1) str
let itoa n =
    if      n == 0
    then    "0"
    else    let rec do n out =
                if n == 0
                then implode out
                else do (n / 10) (chr (n rem 10 + ord "0") : out)
            in do n []
let atoi str =
    map (fun x -> ord x - ord "0") (explode str) >>
        foldl (fun prev x -> prev * 10 + x) 0
    
let digit? = (between (ord "0") (ord "9")) . ord
let lowercase? = (between (ord "a") (ord "z")) . ord
let uppercase? = (between (ord "A") (ord "Z")) . ord
let alphabetical? x = lowercase? x or uppercase? x
let alphanumeric? x = alphabetical? x or digit? x
in
splitat 3 [1,2,3,4,5,6]



