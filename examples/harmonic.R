# By Andrew Hart.

harmonicNumber <- local({
    computed <- cumsum(1/(1:10)) #precompute first 10 harmonic numbers
    function(n) {
        if (!is.numeric(n) || length(n)==0 || any(n<1 | n!=floor(n)))
            stop("n must only contain positive integers")
        max <- max(n)
        if (max>length(computed)) {
            curMax <- length(computed)
            computed[(curMax+1L):max] <- computed[curMax] +
                cumsum(1/((curMax+1L):max))
        } #if
        computed[n] #return requested harmonic numbers
    } #function
}) #local 

