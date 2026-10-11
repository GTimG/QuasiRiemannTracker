import test from "node:test";
import assert from "node:assert/strict";
import { syncPRLabels } from "../verifier/pr-labels.mjs";

const repository = "GTimG/QuasiRiemannTracker";
const number = 15;
const classification = { proof: true, maintenance: false };
const response = (body, status = 200) =>
  new Response(JSON.stringify(body), {
    status,
    headers: { "Content-Type": "application/json" },
  });

function setup(t, { current = [], existing = [], intercept } = {}) {
  const originalToken = process.env.GITHUB_TOKEN;
  process.env.GITHUB_TOKEN = "test-token";
  t.after(() => {
    if (originalToken === undefined) delete process.env.GITHUB_TOKEN;
    else process.env.GITHUB_TOKEN = originalToken;
  });
  const state = {
    current: new Set(current),
    existing: new Set(existing),
    calls: [],
  };
  t.mock.method(globalThis, "fetch", async (input, options = {}) => {
    const url = new URL(input);
    assert.equal(url.origin, "https://api.github.com");
    assert.equal(options.headers.Authorization, "Bearer test-token");
    const call = {
      path: url.pathname,
      query: url.searchParams,
      method: options.method ?? "GET",
      body: options.body ? JSON.parse(options.body) : undefined,
    };
    state.calls.push(call);
    const intercepted = await intercept?.(call, state);
    if (intercepted) return intercepted;
    const repoRoute = `/repos/${repository}/labels`;
    const issueRoute = `/repos/${repository}/issues/${number}/labels`;
    if (call.path === issueRoute && call.method === "GET") {
      assert.equal(call.query.get("per_page"), "100");
      const page = Number(call.query.get("page"));
      return response(
        [...state.current]
          .slice((page - 1) * 100, page * 100)
          .map((name) => ({ name })),
      );
    }
    if (call.path.startsWith(`${repoRoute}/`) && call.method === "GET") {
      const name = decodeURIComponent(call.path.slice(repoRoute.length + 1));
      return state.existing.has(name)
        ? response({ name })
        : response({ message: "Not Found" }, 404);
    }
    if (call.path === repoRoute && call.method === "POST") {
      assert.match(call.body.color, /^[a-f0-9]{6}$/);
      assert.equal(typeof call.body.description, "string");
      state.existing.add(call.body.name);
      return response({ name: call.body.name }, 201);
    }
    if (call.path === issueRoute && call.method === "POST") {
      for (const name of call.body.labels) state.current.add(name);
      return response([...state.current].map((name) => ({ name })));
    }
    if (call.path.startsWith(`${issueRoute}/`) && call.method === "DELETE") {
      const name = decodeURIComponent(call.path.slice(issueRoute.length + 1));
      state.current.delete(name);
      return response([...state.current].map((name) => ({ name })));
    }
    throw Error(`Unexpected request: ${call.method} ${call.path}`);
  });
  return state;
}

test("proof changes create and apply the new-bound label", async (t) => {
  const state = setup(t, { current: ["help wanted"] });
  assert.deepEqual(await syncPRLabels(repository, number, classification), [
    "new-bound",
  ]);
  assert.deepEqual([...state.current], ["help wanted", "new-bound"]);
  assert.deepEqual([...state.existing], ["new-bound"]);
  assert.equal(
    state.calls.some((call) => call.method === "PUT"),
    false,
  );
});

test("mixed changes create and apply both managed labels", async (t) => {
  const state = setup(t);
  assert.deepEqual(
    await syncPRLabels(repository, number, { proof: true, maintenance: true }),
    ["new-bound", "maintenance"],
  );
  assert.deepEqual([...state.current], ["new-bound", "maintenance"]);
  assert.deepEqual([...state.existing], ["new-bound", "maintenance"]);
});

test("maintenance replaces only stale managed labels", async (t) => {
  const state = setup(t, {
    current: ["review needed", "new-bound", "new-bound-discussion"],
    existing: ["new-bound", "maintenance"],
  });
  await syncPRLabels(repository, number, { proof: false, maintenance: true });
  assert.deepEqual(
    [...state.current],
    ["review needed", "new-bound-discussion", "maintenance"],
  );
  assert.equal(
    state.calls.filter((call) => call.method === "DELETE").length,
    1,
  );
});

test("repeated runs preserve managed and unrelated labels", async (t) => {
  const state = setup(t, { current: ["keep me"] });
  await syncPRLabels(repository, number, classification);
  state.calls.length = 0;
  await syncPRLabels(repository, number, classification);
  assert.ok(state.calls.every((call) => call.method === "GET"));
  assert.deepEqual([...state.current], ["keep me", "new-bound"]);
});

test("unrelated labels added concurrently are preserved", async (t) => {
  const state = setup(t, {
    current: ["maintenance"],
    existing: ["new-bound"],
    intercept(call, current) {
      if (call.method === "POST" && call.body.labels)
        current.current.add("human-added-during-run");
    },
  });
  await syncPRLabels(repository, number, classification);
  assert.deepEqual([...state.current], ["human-added-during-run", "new-bound"]);
});

test("all PR label pages are read before removing stale managed labels", async (t) => {
  const unrelated = Array.from({ length: 100 }, (_, index) => `human-${index}`);
  const state = setup(t, {
    current: [...unrelated, "maintenance"],
    existing: ["new-bound"],
  });
  await syncPRLabels(repository, number, classification);
  assert.deepEqual([...state.current], [...unrelated, "new-bound"]);
  assert.ok(state.calls.some((call) => call.query.get("page") === "2"));
});

test("concurrent repository-label creation is confirmed after a 422", async (t) => {
  const state = setup(t, {
    intercept(call, current) {
      if (call.method === "POST" && call.path.endsWith(`/labels`)) {
        if (call.body.name) {
          current.existing.add(call.body.name);
          return response({ message: "already_exists" }, 422);
        }
      }
    },
  });
  await syncPRLabels(repository, number, classification);
  assert.deepEqual([...state.current], ["new-bound"]);
  assert.equal(
    state.calls.filter((call) => call.path.endsWith("/labels/new-bound"))
      .length,
    2,
  );
});

test("requires label existence after a 422 creation response", async (t) => {
  setup(t, {
    intercept(call) {
      if (call.method === "POST" && call.body.name)
        return response({ message: "invalid" }, 422);
    },
  });
  await assert.rejects(syncPRLabels(repository, number, classification), /404/);
});

test("concurrently removed stale labels may return 404", async (t) => {
  setup(t, {
    current: ["maintenance"],
    existing: ["new-bound"],
    intercept(call) {
      if (call.method === "DELETE") return response({}, 404);
    },
  });
  await assert.doesNotReject(syncPRLabels(repository, number, classification));
});

test("propagates HTTP and transport failures", async (t) => {
  const state = setup(t, {
    intercept(call) {
      if (call.method === "POST") return response({}, 403);
    },
  });
  await assert.rejects(syncPRLabels(repository, number, classification), /403/);
  state.calls.length = 0;
  t.mock.method(globalThis, "fetch", async () => {
    throw Error("connection failed");
  });
  await assert.rejects(
    syncPRLabels(repository, number, classification),
    /connection failed/,
  );
});

test("propagates PR label addition and removal failures", async (t) => {
  let failedMethod = "POST";
  setup(t, {
    current: ["maintenance"],
    existing: ["new-bound"],
    intercept(call) {
      if (call.method === failedMethod) return response({}, 503);
    },
  });
  await assert.rejects(syncPRLabels(repository, number, classification), /503/);
  failedMethod = "DELETE";
  await assert.rejects(syncPRLabels(repository, number, classification), /503/);
});

test("an empty classification removes managed labels and preserves unrelated labels", async (t) => {
  const state = setup(t, {
    current: ["new-bound", "maintenance", "bug"],
  });
  assert.deepEqual(
    await syncPRLabels(repository, number, {
      proof: false,
      maintenance: false,
    }),
    [],
  );
  assert.deepEqual([...state.current], ["bug"]);
});

test("validates identity, classification and token before API use", async (t) => {
  const state = setup(t);
  for (const invalid of [
    "../owner/repo",
    "owner/..",
    "owner/repo?x=y",
    "owner/repo\n",
    "owner",
  ])
    await assert.rejects(
      syncPRLabels(invalid, number, classification),
      /Invalid/,
    );
  for (const invalid of [0, -1, 1.5, "15", Number.MAX_SAFE_INTEGER + 1])
    await assert.rejects(
      syncPRLabels(repository, invalid, classification),
      /Invalid/,
    );
  for (const invalid of [
    null,
    {},
    [],
    { proof: true },
    { proof: 1, maintenance: false },
  ])
    await assert.rejects(syncPRLabels(repository, number, invalid), /Invalid/);
  delete process.env.GITHUB_TOKEN;
  await assert.rejects(
    syncPRLabels(repository, number, classification),
    /GITHUB_TOKEN/,
  );
  assert.equal(state.calls.length, 0);
});

test("rejects malformed label responses", async (t) => {
  setup(t, {
    intercept(call) {
      if (call.path.includes(`/issues/`)) return response([{ id: 1 }]);
    },
  });
  await assert.rejects(
    syncPRLabels(repository, number, classification),
    /Unexpected GitHub PR labels/,
  );
});
