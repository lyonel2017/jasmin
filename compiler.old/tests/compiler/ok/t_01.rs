#![allow(non_upper_case_globals)]
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_mut)]
#![allow(unused_assignments)]

#[macro_use] extern crate jasmin;

rust! {
    use jasmin::jasmin::*;
    use jasmin::U64::*;
    
}

rust! {
    mod test {
        use jasmin::jasmin::*;
        use jasmin::U64::*;

        #[test]
        fn test1() {
            ::foo3(0.to_jval());
        }
    }
}

rust! {
    fn foo1(x: stack! (b64)) -> (stack! (b64), reg! (b64), reg! (b1)) {
        return (x,x,b1!(false));
    }
}

const n : uint = 10;

decl! { fn foo1(stack! (b64)) -> (stack! (b64), reg! (b64), reg! (b1)); }

// nothing
fn foo3(_x: stack! (b64)) {
}

// decl only
pub fn foo4(_x: stack! (b64)) {
    var! {
        _y: stack! (b64); // will not be printed
    }
}

// body only
pub fn foo5(mut x: stack! (b64)) {
    code! {
        x = add(x,x);
    }
}


// return only
fn foo6(x: stack! (b64)) -> stack! (b64) {
    return x
}


// deck + body
fn foo7(mut x: stack! (b64)) {
    var! {
        y: stack! (b64);
    }
    
    code! {
        y = b64!(n);
        x = add(x,y);
    }
}

// decl + return
fn foo8(x : stack! (b64)) -> (stack! (b64),stack! (b64)) {
    var! {
        _y: stack! (b64);
    }
    return (x,x)
}

// body + return
fn foo9(mut x: stack! (b64)) -> stack! (b64) {
    code! {
        x = add(x,x);
    }

    return x
}

// decl + body + return
fn foo10(mut x: stack! (b64), y: stack! (b64), mut z: reg! (b1)) -> stack! (b64) {
    var! {
        w: stack! (b64);
        j: inline! (uint);
    }
    
    code! {
        w = x;
        (w,x,z) = foo1(x);
        inl!{ foo4(x) };
        x = b64!(5);
        w = add(w,x);
        for j in (0..10) {
            if (j == 5) {
                (z,x) = add_cf(x,w);
                (z,x) = add_cf(x,y);
            }
        }
        x = adc(x,x,z);
    }
    return x
}

/*
START:CMD
ARG="typecheck,cargo_test,print[roundtrip][]"
END:CMD
*/