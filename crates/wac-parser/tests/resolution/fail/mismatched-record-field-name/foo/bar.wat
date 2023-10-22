(component
  (instance (import "x")
    (type (record (field "a" u8) (field "b" u16) (field "c" u32)))
    (export "r" (type (eq 0)))
  )
)
