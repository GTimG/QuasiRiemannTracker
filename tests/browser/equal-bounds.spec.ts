import { expect, test } from "@playwright/test";
import { record, routeCatalogue } from "./catalogue-fixture";
import { withEqualBounds } from "../../scripts/equal-bounds.mjs";

test("open the other proof of the same endpoint from the submission list", async ({
  page,
}) => {
  const records = withEqualBounds([
    record({
      id: "first-root",
      title: "First root proof",
      exact_bound: "root([-2,0,1],1/1,2/1)",
      theta: { numerator: "3", denominator: "2" },
    }),
    record({
      id: "second-root",
      title: "Second root proof",
      exact_bound: "root([-2,-2,1,1],7/5,3/2)",
      theta: { numerator: "10", denominator: "7" },
    }),
    record({
      id: "witness-only",
      title: "Rational proof",
      theta: { numerator: "3", denominator: "2" },
    }),
  ]);
  await routeCatalogue(page, { schema_version: 1, records });
  await page.goto("/?tab=submissions&mode=list");
  await expect(
    page.getByText("Same exact bound as 1 other proof", { exact: true }),
  ).toHaveCount(2);
  await page
    .getByRole("button", { name: "First root proof", exact: true })
    .click();
  const detail = page.locator(".proof-detail");
  await expect(
    detail.getByRole("heading", {
      name: "Other proofs of the same exact bound",
    }),
  ).toBeVisible();
  await detail
    .getByRole("button", { name: "Second root proof", exact: true })
    .click();
  await expect(
    detail.getByRole("heading", { name: "Second root proof", exact: true }),
  ).toBeVisible();
  await expect(
    detail.getByRole("button", { name: "First root proof", exact: true }),
  ).toBeVisible();
});
