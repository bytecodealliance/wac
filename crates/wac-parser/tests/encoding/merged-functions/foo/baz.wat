(component
  (import "foo:bar/baz" (instance
    (type (record (field "x" u32)))
    (export "x" (type (eq 0)))
    (export "z" (func (param "x" 1)))
  ))
)
