# By Andrew Hart.

simulate.markov.chain.1 <- function(n, trans.mat, init.dist=NULL, 
states=colnames(trans.mat)) 
{ 
  if (is.null(init.dist)) 
  { 
    e <- eigen(t(trans.mat)) 
    init.dist <- abs(as.double(e$vectors[,1])) 
    init.dist <- init.dist/sum(init.dist) 
  }
  disturbance <- runif(n) #generate noise 
  samplePath <- numeric(n) 
  #precalculate initial and conditional cdfs 
  init.cdf <- cumsum(init.dist[-length(init.dist)]) 
  trans.cdf <- t(apply(trans.mat[, -dim(trans.mat)[2], drop=FALSE], 1, cumsum))
  #correctly label the rows and columns 
  rownames(trans.cdf) <- rownames(trans.mat) 
  samplePath[1]<-sum(init.cdf<disturbance[1])+1 
  for (i in 2:n) 
  samplePath[i]< sum(trans.cdf[samplePath[i-1],]<disturbance[i])+1 
  return(states[samplePath]) 
} #function



simulate.markov.chain.2 <- function(n, trans.mat, 
  init.dist=NULL, states=colnames(trans.mat)) 
{ 
  if (is.null(init.dist)) 
  { 
    e <- eigen(t(trans.mat)) 
    init.dist <- abs(as.double(e$vectors[,1])) 
    init.dist <- init.dist/sum(init.dist) 
  }
  disturbance <- runif(n) #generate noise 
  samplePath <- numeric(n) 
  #Precalculate initial and conditional cdfs 
  init.cdf<-cumsum(init.dist[-length(init.dist)]) 
  trans.cdf <- t(apply(trans.mat[, -dim(trans.mat)[2]], 1, cumsum)) 
  init.state <- sum(init.cdf<disturbance[1])+1
  disturbance <- disturbance[-1] 
  #Precompute intermediate values 
  tr<-matrix(1, ncol=n-1, nrow=length(states), dimnames=list(states)) 
  for (j in 1:length(states)) 
    for (i in 1:dim(trans.cdf)[2]) 
      tr[j,] <- tr[j,] + (trans.cdf[j,i]<disturbance) 
  samplePath[1] <- init.state 
  for (i in 1:(n-1)) 
    #get next state using transition probs 
    samplePath[i+1] <- tr[samplePath[i], i] 
  return(states[samplePath]) 
}

