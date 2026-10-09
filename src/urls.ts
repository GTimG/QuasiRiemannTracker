export const publicUrl = (path: string) =>
  /^https:\/\//.test(path)
    ? path
    : import.meta.env.BASE_URL + path.replace(/^\//, "");
