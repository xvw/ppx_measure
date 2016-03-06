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

