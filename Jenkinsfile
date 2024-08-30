// Copyright (c) 2024 Fantom Foundation
//
// Use of this software is governed by the Business Source License included
// in the LICENSE file and at fantom.foundation/bsl11.
//
// Change Date: 2028-4-16
//
// On the date above, in accordance with the Business Source License, use of
// this software will be governed by the GNU Lesser General Public License v3.

pipeline {
    agent { label 'db-small-ssd' }

    options {
        timestamps ()
        timeout(time: 2, unit: 'HOURS')
    }

    environment {
        GOROOT = '/usr/lib/go-1.21/'
        GOMEMLIMIT = '5GiB'
    }

    stages {
        stage('Validate commit') {
            steps {
                script {
                    def CHANGE_REPO = sh (script: "basename -s .git `git config --get remote.origin.url`", returnStdout: true).trim()
                    build job: '/Utils/Validate-Git-Commit', parameters: [
                        string(name: 'Repo', value: "${CHANGE_REPO}"),
                        string(name: 'Branch', value: "${env.CHANGE_BRANCH}"),
                        string(name: 'Commit', value: "${GIT_COMMIT}")
                    ]
                }
            }
        }

        stage('Run tests') {
            stages {
                stage('Check license headers') {
                    steps {
                        sh 'cd scripts/license && ./add_license_header.sh --check'
                    }
                }

                stage('Check Go sources formatting') {
                    steps {
                        sh 'diff=`${GOROOT}/bin/gofmt -s -d .` && echo "$diff" && test -z "$diff"'
                    }
                }

                stage('Build Go') {
                    steps {
                        sh 'go build -v ./...'
                    }
                }

                stage('Run Go tests') {
                    steps {
                        sh 'go test ./... -parallel 1 -timeout 60m'
                    }
                }

                stage('Run Mpt Go Stress Test') {
                    steps {
                        sh 'go run ./database/mpt/tool stress-test --num-blocks 2000'
                    }
                }
            }
        }
    }
}
