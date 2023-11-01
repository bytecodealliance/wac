(component
  (instance (import "x")
    (export "r" (type (sub resource)))
    (type $own-r (own 0))
    (export "f" (func (param "r" $own-r)))
    (export "[constructor]r" (func (result $own-r)))
  )
)
