(component
  (import "test:dep/iface@0.2.1"
    (instance $i
      (export "foo" (func))
    )
  )
  (alias export $i "foo" (func $foo))
  (export "bar" (func $foo))
)
