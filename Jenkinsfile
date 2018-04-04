pipeline {
  agent any
  environment {
      COQ_INTERP = "${env.WORKSPACE}"
      RSCRIPT = "R"
  }
  stages {
    stage('build') {
      steps {
        sh 'eval `opam config env`'
        sh 'make tlc'
        sh 'make'
      }
        
    }
    stage('test') {
        steps {
            sh ". ${env.PYTHON_ENV}/activate && ${env.WORKSPACE}/compare/run_all.py ${env.RTESTS} ${env.PROVER_OUT}"
        }
    }
  }
}