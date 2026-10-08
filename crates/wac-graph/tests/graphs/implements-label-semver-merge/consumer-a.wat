(component
  (type (instance
    (type (func (param "message" string)))
    (export "log" (func (type 0)))))
  (import "primary" (implements "test:test/logger@0.2.0") (instance (type 0)))
)
