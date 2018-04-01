pipeline {
  agent any
  stages {
    stage('build') {
      steps {
        sh 'make tlc'
        sh 'make'
      }
    }
  }
}