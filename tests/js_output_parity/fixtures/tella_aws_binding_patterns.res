type client
type clientOptions = {
  region: string,
}

@module("@aws-sdk/client-s3") @new
external makeClient: clientOptions => client = "S3Client"

type putObjectInput = {
  @as("Bucket")
  bucket: string,
  @as("Key")
  key: string,
  @as("Body")
  body: string,
  @as("StorageClass")
  storageClass: string,
}

type putObjectOutput = {
  @as("ETag")
  eTag: string,
}

type putObjectCommand

@module("@aws-sdk/client-s3") @new
external makePutObjectCommand: putObjectInput => putObjectCommand = "PutObjectCommand"

@send external sendPut: (client, putObjectCommand) => promise<putObjectOutput> = "send"

type multipartUpload = {
  @as("Parts")
  parts: array<string>,
}

type completeMultipartInput = {
  @as("Bucket")
  bucket: string,
  @as("Key")
  key: string,
  @as("UploadId")
  uploadId: string,
  @as("MultipartUpload")
  multipartUpload: multipartUpload,
}

type completeMultipartCommand

@module("@aws-sdk/client-s3") @new
external makeCompleteMultipartCommand: completeMultipartInput => completeMultipartCommand =
  "CompleteMultipartUploadCommand"

@send
external sendComplete: (client, completeMultipartCommand) => promise<putObjectOutput> = "send"

type upload
type uploadOptions = {
  client: client,
  params: putObjectInput,
}
type progress = {
  loaded: float,
  total: float,
}

@module("@aws-sdk/lib-storage") @new external makeUpload: uploadOptions => upload = "Upload"
@send external done_: (upload, unit) => promise<unit> = "done"
@send external onProgress: (upload, @as("httpUploadProgress") _, progress => unit) => unit = "on"

@module("shaka-player") @scope("polyfill") external installAll: unit => unit = "installAll"

@module("shaka-player") @scope(("net", "NetworkingEngine", "RequestType")) @val
external requestTypeManifest: string = "MANIFEST"

let client = makeClient({region: "eu-west-1"})

let putInput = {
  bucket: "videos",
  key: "story.mp4",
  body: "payload",
  storageClass: "STANDARD",
}

let putCommand = makePutObjectCommand(putInput)

let putResult = client->sendPut(putCommand)

let completeCommand = makeCompleteMultipartCommand({
  bucket: "videos",
  key: "story.mp4",
  uploadId: "upload-1",
  multipartUpload: {parts: ["a", "b"]},
})

let completeResult = client->sendComplete(completeCommand)

let upload = makeUpload({client, params: putInput})

let progressHandler = value => {
  Console.log2(value.loaded, value.total)
}

let progressRegistration = upload->onProgress(progressHandler)

let uploadDone = upload->done_()

let setupShaka = () => {
  installAll()
  requestTypeManifest
}
