module hello where
    -- tabs are limiters, no {}
    data Greeting : Set where
        hello : Greeting
        ahoy : Greeting
        Salutations : Greeting
    greet : Greeting -- greet is going to return something of type = greeting
    greet = hello -- constant function, greet always returns hello
    
    greet2 : Greeting
    greet2 = ahoy

    greet3 : Greeting
    greet3 =  {! ,  !}  -- ctr c, ctrl n will ask for the normal function
 




