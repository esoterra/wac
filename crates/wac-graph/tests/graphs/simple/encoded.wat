(component
  (type (;0;)
    (instance)
  )
  (import "i1" (instance (;0;) (type 0)))
  (type (;1;)
    (instance)
  )
  (import "merged" (instance (;1;) (type 1)))
  (type (;2;)
    (instance)
  )
  (import "i2" (instance (;2;) (type 2)))
  (type (;3;) (func))
  (import "my-foo" (func $my-foo (;0;) (type 3)))
  (component (;0;)
    (type (;0;) (func))
    (type (;1;) (func))
    (import "foo" (func (;0;) (type 1)))
    (type (;2;)
      (instance)
    )
    (import "i1" (instance (;0;) (type 2)))
    (type (;3;)
      (instance)
    )
    (import "merged" (instance (;1;) (type 3)))
    (export (;1;) "bar" (func 0))
    (export (;4;) "f" (type 0))
  )
  (instance $foo (;3;) (instantiate 0
      (with "foo" (func $my-foo))
      (with "i1" (instance 0))
      (with "merged" (instance 1))
    )
  )
  (alias export $foo "bar" (func $e (;1;)))
  (component (;1;)
    (type (;0;) (func))
    (import "e" (func (;0;) (type 0)))
    (type (;1;)
      (instance)
    )
    (import "i2" (instance (;0;) (type 1)))
    (type (;2;)
      (instance)
    )
    (import "merged" (instance (;1;) (type 2)))
    (export (;1;) "e" (func 0))
  )
  (instance $bar (;4;) (instantiate 1
      (with "e" (func $e))
      (with "i2" (instance 2))
      (with "merged" (instance 1))
    )
  )
  (alias export $bar "e" (func $e2 (;2;)))
  (export (;3;) "e2" (func $e2))
)
