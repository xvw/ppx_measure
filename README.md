# ppx_measure

> Provide a syntactic extension to unit of measure representation using Phantom types.

## Usage

For using this ppx extension, your ml file must begin by `[%%use_measure]`. This extension 
point will be substitute by a module "Measure" with all of types and combinators (in relation 
of the units).

### Declaring a type as an unit of measure

Measurement are grouped by `type ... and ... and` structure. 
```
type a [@@measure]
and  b [@@measure coersion_function]
and  c [@@measure coersion_function]
etc ...
```

The coersion_function is a lambda to pass from a to b, or a to c. 

For example, let's define "cm" family : 

```ocaml
[%%use_measure]

type cm [@@measure]
and  m  [@@measure fun cm -> cm *. 100.  ]
and  km [@@measure fun cm -> cm *. 1000. ]

```

This code will generate this code : 

```ocaml
module Measure :
  sig
    type ('base,'subtype) t
    val to_float : ('base,'subtype) t -> float
    val (+) : ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val (-) : ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val ( * ) :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val (/) : ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val ( ** ) :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val sqrt : ('base,'subtype) t -> ('base,'subtype) t
    val exp : ('base,'subtype) t -> ('base,'subtype) t
    val log : ('base,'subtype) t -> ('base,'subtype) t
    val log10 : ('base,'subtype) t -> ('base,'subtype) t
    val expm1 : ('base,'subtype) t -> ('base,'subtype) t
    val cos : ('base,'subtype) t -> ('base,'subtype) t
    val sin : ('base,'subtype) t -> ('base,'subtype) t
    val tan : ('base,'subtype) t -> ('base,'subtype) t
    val acos : ('base,'subtype) t -> ('base,'subtype) t
    val asin : ('base,'subtype) t -> ('base,'subtype) t
    val atan : ('base,'subtype) t -> ('base,'subtype) t
    val atan2 :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val hypot :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val cosh : ('base,'subtype) t -> ('base,'subtype) t
    val sinh : ('base,'subtype) t -> ('base,'subtype) t
    val tanh : ('base,'subtype) t -> ('base,'subtype) t
    val ceil : ('base,'subtype) t -> ('base,'subtype) t
    val floor : ('base,'subtype) t -> ('base,'subtype) t
    val abs_float : ('base,'subtype) t -> ('base,'subtype) t
    val copysign :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val mod_float :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    type km = ([ `cm ],[ `km ]) t
    type m = ([ `cm ],[ `m ]) t
    type cm = ([ `cm ],[ `cm ]) t
    val to_km : float -> km
    val to_m : float -> m
    val to_cm : float -> cm
    val km_of_cm : cm -> km
    val m_of_cm : cm -> m
  end =
  struct
    type ('base,'subtype) t = float
    let to_float x = x
    let (+) = (+.)
    let (-) = (-.)
    let ( * ) = ( *. )
    let (/) = (/.)
    let ( ** ) = ( ** )
    let sqrt = sqrt
    let exp = exp
    let log = log
    let log10 = log10
    let expm1 = expm1
    let cos = cos
    let sin = sin
    let tan = tan
    let acos = acos
    let asin = asin
    let atan = atan
    let atan2 = atan2
    let hypot = hypot
    let cosh = cosh
    let sinh = sinh
    let tanh = tanh
    let ceil = ceil
    let floor = floor
    let copysign = copysign
    let abs_float = abs_float
    let mod_float = mod_float
    type km = ([ `cm ],[ `km ]) t
    let to_km x = x
    let km_of_cm cm = cm *. 1000.
    type m = ([ `cm ],[ `m ]) t
    let to_m x = x
    let m_of_cm cm = cm *. 100.
    type cm = ([ `cm ],[ `cm ]) t
    let to_cm x = x
  end
``` 

You can define multiple unit of measure : 

```ocaml
[%%use_measure]

type cm [@@measure]
and  m  [@@measure fun cm -> cm *. 100.  ]
and  km [@@measure fun cm -> cm *. 1000. ]


type cl [@@measure]
and  l  [@@measure fun cl -> cl *. 100.  ]
and  kl [@@measure fun cl -> cl *. 1000. ]


type euro   [@@measure]
and  dollar [@@measure fun euro -> euro /. 1.0993 ] 
```

to produce : 

```ocaml
module Measure :
  sig
    type ('base,'subtype) t
    val to_float : ('base,'subtype) t -> float
    val (+) : ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val (-) : ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val ( * ) :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val (/) : ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val ( ** ) :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val sqrt : ('base,'subtype) t -> ('base,'subtype) t
    val exp : ('base,'subtype) t -> ('base,'subtype) t
    val log : ('base,'subtype) t -> ('base,'subtype) t
    val log10 : ('base,'subtype) t -> ('base,'subtype) t
    val expm1 : ('base,'subtype) t -> ('base,'subtype) t
    val cos : ('base,'subtype) t -> ('base,'subtype) t
    val sin : ('base,'subtype) t -> ('base,'subtype) t
    val tan : ('base,'subtype) t -> ('base,'subtype) t
    val acos : ('base,'subtype) t -> ('base,'subtype) t
    val asin : ('base,'subtype) t -> ('base,'subtype) t
    val atan : ('base,'subtype) t -> ('base,'subtype) t
    val atan2 :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val hypot :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val cosh : ('base,'subtype) t -> ('base,'subtype) t
    val sinh : ('base,'subtype) t -> ('base,'subtype) t
    val tanh : ('base,'subtype) t -> ('base,'subtype) t
    val ceil : ('base,'subtype) t -> ('base,'subtype) t
    val floor : ('base,'subtype) t -> ('base,'subtype) t
    val abs_float : ('base,'subtype) t -> ('base,'subtype) t
    val copysign :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    val mod_float :
      ('base,'subtype) t -> ('base,'subtype) t -> ('base,'subtype) t
    type dollar = ([ `euro ],[ `dollar ]) t
    type euro = ([ `euro ],[ `euro ]) t
    type km = ([ `cm ],[ `km ]) t
    type cl = ([ `cl ],[ `cl ]) t
    type kl = ([ `cl ],[ `kl ]) t
    type m = ([ `cm ],[ `m ]) t
    type cm = ([ `cm ],[ `cm ]) t
    type l = ([ `cl ],[ `l ]) t
    val to_dollar : float -> dollar
    val to_euro : float -> euro
    val to_km : float -> km
    val to_cl : float -> cl
    val to_kl : float -> kl
    val to_m : float -> m
    val to_cm : float -> cm
    val to_l : float -> l
    val dollar_of_euro : euro -> dollar
    val km_of_cm : cm -> km
    val kl_of_cl : cl -> kl
    val m_of_cm : cm -> m
    val l_of_cl : cl -> l
  end =
  struct
    type ('base,'subtype) t = float
    let to_float x = x
    let (+) = (+.)
    let (-) = (-.)
    let ( * ) = ( *. )
    let (/) = (/.)
    let ( ** ) = ( ** )
    let sqrt = sqrt
    let exp = exp
    let log = log
    let log10 = log10
    let expm1 = expm1
    let cos = cos
    let sin = sin
    let tan = tan
    let acos = acos
    let asin = asin
    let atan = atan
    let atan2 = atan2
    let hypot = hypot
    let cosh = cosh
    let sinh = sinh
    let tanh = tanh
    let ceil = ceil
    let floor = floor
    let copysign = copysign
    let abs_float = abs_float
    let mod_float = mod_float
    type dollar = ([ `euro ],[ `dollar ]) t
    let to_dollar x = x
    let dollar_of_euro euro = euro /. 1.0993
    type euro = ([ `euro ],[ `euro ]) t
    let to_euro x = x
    type km = ([ `cm ],[ `km ]) t
    let to_km x = x
    let km_of_cm cm = cm *. 1000.
    type cl = ([ `cl ],[ `cl ]) t
    let to_cl x = x
    type kl = ([ `cl ],[ `kl ]) t
    let to_kl x = x
    let kl_of_cl cl = cl *. 1000.
    type m = ([ `cm ],[ `m ]) t
    let to_m x = x
    let m_of_cm cm = cm *. 100.
    type cm = ([ `cm ],[ `cm ]) t
    let to_cm x = x
    type l = ([ `cl ],[ `l ]) t
    let to_l x = x
    let l_of_cl cl = cl *. 100.
  end 

```

## Using measure (some examples)

### Standard usage

```ocaml
[%%use_measure]

type cm [@@measure]
and  m  [@@measure fun cm -> cm *. 100.  ]
and  km [@@measure fun cm -> cm *. 1000. ]

let a = Measure.to_cm 1.0 
let b = Measure.to_cm 2.0 
let c = Measure.(a + b)

let d = Measure.to_km 2.0 
let e = Measure.(a + d) (* This code crash *)
```

### With extension point

```ocaml
[%%use_measure]

type cm [@@measure]
and  m  [@@measure fun cm -> cm *. 100.  ]
and  km [@@measure fun cm -> cm *. 1000. ]

let%cm a = 1.0 
let%cm b = 2.0 
let c = Measure.(a + b)

let%km d = 2.0 
let e = Measure.(a + d) (* This code crash *)
```

`let%f a = x` is rewritted to `let a = Measure.to_f x`
