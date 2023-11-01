(component
  (instance (import "x")
    (export "x" (type (sub resource)))
    (export "y" (type (sub resource)))
    (type $own-x (own 0))
    (export "f" (func (param "x" $own-x)))
  )
)
