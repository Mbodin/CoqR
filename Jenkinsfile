pipeline {
  agent any
  stages {
    stage('build') {
      steps {
        sh 'eval `opam config env`'
        sh 'make tlc'
        sh 'make'
      }
    }
    stage('test') {
      parallel {
        stage('Test R') {
          steps {
            sh ". ${env.PYTHON_ENV}/activate && ${env.WORKSPACE}/compare/run_all.py ${env.RTESTS} --server -t 'R 3.4.2 Tests'"
          }
        }
        stage('Test fastR') {
          steps {
            sh '". ${env.PYTHON_ENV}/activate && ${env.WORKSPACE}/compare/run_all.py ${env.TESTS_FOLDER}/fastr --server -t \'fastR Tests\'"'
          }
        }
      }
    }
  }
  environment {
    COQ_INTERP = "${env.WORKSPACE}"
    RSCRIPT = 'R'
  }
}