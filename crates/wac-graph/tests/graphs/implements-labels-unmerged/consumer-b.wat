(component
  (type (instance
    (type (func (param "message" string)))
    (export "log" (func (type 0)))
    (type (func))
    (export "flush" (func (type 1)))))
  (import "backup" (implements "test:test/logger@0.2.1") (instance (type 0)))
)
