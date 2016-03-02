type cm [@@measure]

type km [@@measure  cm, fun x -> x /. 1000.]
type litres [@@measure]

type truc = float

let x = 10

