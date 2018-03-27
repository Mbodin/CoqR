pipeline {
  agent any
  stages {
    stage('build') {
      steps {
        git 'submodule update --init'
        sh 'make tlc'
        sh 'make'
      }
    }
  }
}
