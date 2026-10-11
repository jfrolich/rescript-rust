%%raw(`
function outputParityScopedClient() {
  return {
    customers: {
      create(options) {
        return "customer:" + options.name + ":" + (options.metadata.orgID || "")
      },
      update(id, payload) {
        return "update:" + id + ":" + (payload.email || "")
      }
    },
    billingPortal: {
      sessions: {
        create(options) {
          return "session:" + options.customer + ":" + options.return_url
        }
      }
    }
  }
}
`)

type client

type metadata = {
  userID?: string,
  orgID?: string,
  referral?: string,
}

type customerOptions = {
  name: string,
  email: option<string>,
  metadata: metadata,
}

type updatePayload = {
  email?: string,
  metadata?: metadata,
}

type lineItem = {
  id: string,
  price: string,
  quantity: int,
}

type discount = {
  promotion_code: option<string>,
  coupon: option<string>,
}

type subscriptionUpdateConfirm = {
  subscription: string,
  items: array<lineItem>,
  discounts?: array<discount>,
}

type flowData = {
  @as("type")
  type_: string,
  subscription_update_confirm?: subscriptionUpdateConfirm,
}

type sessionOptions = {
  customer: string,
  return_url: string,
  flow_data?: flowData,
}

@module("stripe") @new external makeStripe: string => client = "default"
@val external makeLocalClient: unit => client = "outputParityScopedClient"

module Customers = {
  @send @scope("customers")
  external create: (client, customerOptions) => string = "create"

  @send @scope("customers")
  external update: (client, string, updatePayload) => string = "update"
}

module BillingPortal = {
  module Sessions = {
    @send @scope(("billingPortal", "sessions"))
    external create: (client, sessionOptions) => string = "create"
  }
}

module NotionPages = {
  @send @scope("pages")
  external create: (client, JSON.t) => JSON.t = "create"
}

let localClient = makeLocalClient()
let importedClient = makeStripe("secret")

let createdCustomer =
  localClient->Customers.create({
    name: "Ada",
    email: Some("ada@example.com"),
    metadata: {userID: "user_1", orgID: "org_1"},
  })

let updatedCustomer =
  localClient->Customers.update("cus_1", {
    email: "next@example.com",
    metadata: {referral: "invite"},
  })

let createdSession =
  localClient->BillingPortal.Sessions.create({
    customer: "cus_1",
    return_url: "https://example.com/return",
    flow_data: {
      type_: "subscription_update_confirm",
      subscription_update_confirm: {
        subscription: "sub_1",
        items: [{id: "item_1", price: "price_1", quantity: 2}],
        discounts: [{promotion_code: Some("promo"), coupon: None}],
      },
    },
  })

let notionPayload =
  NotionPages.create(
    importedClient,
    JSON.Encode.object(Dict.fromArray([("id", JSON.Encode.string("page"))])),
  )

let allValues = (createdCustomer, updatedCustomer, createdSession, notionPayload)
