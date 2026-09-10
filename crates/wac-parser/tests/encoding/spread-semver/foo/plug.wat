(component
  (core module $m
    (func (export "foo"))
  )
  (core instance $i (instantiate $m))
  (func $foo (canon lift (core func $i "foo")))
  (instance $iface (export "foo" (func $foo)))
  (export "test:dep/iface@0.2.0" (instance $iface))
)
